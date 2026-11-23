-- Prove2me | solution 1 for OptimalTraceDistance.Estimation.rounded_algorithm_realization
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T10:11:32.396056+00:00
-- url     : https://prove2.me/submissions/41c933f1-3459-48d9-b316-05e0b6932565
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OptimalTraceDistance_Estimation_RoundedAlgorithm
import Theorems.Thm_QAlgorithms_Papers_RoadmapL03_keyl_expectedSquaredFrobeniusError

open MeasureTheory
open scoped BigOperators Matrix ComplexOrder ENNReal Kronecker MatrixOrder Classical
noncomputable section
namespace OTDReal
open Matrix OptimalTraceDistance.Estimation

variable {d : ℕ}
abbrev D2 (d : ℕ) := Fin d × Fin d

/-- per-position state of a pair register -/
def pairState (ρ σ : Mat d) : Matrix (D2 d) (D2 d) ℂ := ρ ⊗ₖ σ

def tauB (ρ σ : Mat d) (b : Bool) : Mat d := if b then σ else ρ

/-- splitting a pair register by labels -/
def splitEquiv {m : ℕ} (l : Fin m → Bool) : (Fin m → Fin d) × (Fin m → Fin d) ≃ (Fin m → D2 d) where
  toFun su := fun k => if l k then ((su.2 k), (su.1 k)) else ((su.1 k), (su.2 k))
  invFun p := (fun k => if l k then (p k).2 else (p k).1, fun k => if l k then (p k).1 else (p k).2)
  left_inv su := by
    ext k <;> simp only <;> split_ifs <;> rfl
  right_inv p := by
    funext k; simp only; split_ifs <;> rfl

/-- label embedding of an operator on the selected copies -/
def Emb {m : ℕ} (l : Fin m → Bool) (A : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) :
    Matrix (Fin m → D2 d) (Fin m → D2 d) ℂ :=
  (A ⊗ₖ (1 : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ)).submatrix
    (splitEquiv l).symm (splitEquiv l).symm

lemma Emb_one {m : ℕ} (l : Fin m → Bool) : Emb (d := d) l 1 = 1 := by
  unfold Emb
  rw [Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

lemma Emb_add {m : ℕ} (l : Fin m → Bool) (A B : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) :
    Emb l (A + B) = Emb l A + Emb l B := by
  unfold Emb; rw [Matrix.add_kronecker]; rfl

lemma Emb_smul {m : ℕ} (l : Fin m → Bool) (c : ℂ) (A : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) :
    Emb l (c • A) = c • Emb l A := by
  unfold Emb; rw [Matrix.smul_kronecker]; rfl

lemma Emb_zero {m : ℕ} (l : Fin m → Bool) : Emb (d := d) l 0 = 0 := by
  unfold Emb; simp

lemma Emb_psd {m : ℕ} (l : Fin m → Bool) {A : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ}
    (hA : A.PosSemidef) : (Emb l A).PosSemidef := by
  unfold Emb
  exact (hA.kronecker PosSemidef.one).submatrix _

lemma trace_submatrix_mul {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : κ ≃ ι) (M : Matrix ι ι ℂ) (N : Matrix κ κ ℂ) :
    (M.submatrix e e * N).trace = (M * N.submatrix e.symm e.symm).trace := by
  have h : M.submatrix e e * N = (M * N.submatrix e.symm e.symm).submatrix e e := by
    rw [← Matrix.submatrix_mul_equiv M (N.submatrix e.symm e.symm) e e e]
    simp
  rw [h]
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun i => (M * N.submatrix e.symm e.symm) i i)

/-- the product of pair states, after splitting by labels -/
lemma piKron_split {m : ℕ} (l : Fin m → Bool) (ρ σ : Mat d) :
    (QAlgorithms.piKron m (pairState ρ σ)).submatrix (splitEquiv l) (splitEquiv l) =
      (Matrix.of fun s s' : Fin m → Fin d => ∏ k, tauB ρ σ (l k) (s k) (s' k)) ⊗ₖ
        (Matrix.of fun u u' : Fin m → Fin d => ∏ k, tauB ρ σ (!l k) (u k) (u' k)) := by
  ext ⟨s, u⟩ ⟨s', u'⟩
  simp only [Matrix.submatrix_apply, Matrix.kronecker_apply, QAlgorithms.piKron, Matrix.of_apply,
    splitEquiv, Equiv.coe_fn_mk, pairState]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  cases l k <;> simp [tauB, Matrix.kroneckerMap_apply, mul_comm]

def Tl {m : ℕ} (ρ σ : Mat d) (l : Fin m → Bool) : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ :=
  Matrix.of fun s s' => ∏ k, tauB ρ σ (l k) (s k) (s' k)

lemma trace_prodState {m : ℕ} (f : Fin m → Mat d) :
    (Matrix.of fun u u' : Fin m → Fin d => ∏ k, f k (u k) (u' k)).trace = ∏ k, (f k).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
  rw [Finset.prod_univ_sum]
  rfl

lemma Emb_trace {m : ℕ} (l : Fin m → Bool) (A : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ)
    {ρ σ : Mat d} (hρ : ρ.trace = 1) (hσ : σ.trace = 1) :
    (Emb l A * QAlgorithms.piKron m (pairState ρ σ)).trace = (A * Tl ρ σ l).trace := by
  unfold Emb
  rw [trace_submatrix_mul (splitEquiv l).symm, Equiv.symm_symm, piKron_split,
    ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, Matrix.one_mul, trace_prodState]
  have : ∀ k, (tauB ρ σ (!l k)).trace = 1 := fun k => by cases l k <;> simp [tauB, hρ, hσ]
  simp only [this, Finset.prod_const_one, mul_one]
  rfl

lemma plus_apply (ρ σ : Mat d) (i j : Fin d) : plus ρ σ i j = (2:ℂ)⁻¹ * (ρ i j + σ i j) := by
  show ((2:ℂ)⁻¹ • (ρ + σ)) i j = _
  rw [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]

lemma piKron_plus {m : ℕ} (ρ σ : Mat d) :
    QAlgorithms.piKron m (plus ρ σ) = ∑ l : Fin m → Bool, ((2:ℂ)⁻¹)^m • Tl ρ σ l := by
  ext s s'
  simp only [QAlgorithms.piKron, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, Tl, plus_apply,
    smul_eq_mul]
  have : ∀ k, (2:ℂ)⁻¹ * (ρ (s k) (s' k) + σ (s k) (s' k)) = ∑ b : Bool, (2:ℂ)⁻¹ * tauB ρ σ b (s k) (s' k) := by
    intro k
    rw [Fintype.sum_bool]
    simp only [tauB, if_true, Bool.false_eq_true, if_false]; ring
  simp only [this]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma mixture_trace {m : ℕ} (A : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) {ρ σ : Mat d}
    (hρ : ρ.trace = 1) (hσ : σ.trace = 1) :
    (A * QAlgorithms.piKron m (plus ρ σ)).trace =
      ∑ l : Fin m → Bool, ((2:ℂ)⁻¹)^m * (Emb l A * QAlgorithms.piKron m (pairState ρ σ)).trace := by
  rw [piKron_plus, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Emb_trace l A hρ hσ, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- the label blocks of an operator on labelled copies -/
def pairL {n : ℕ} (b : Fin n → Bool) (z : Fin n → Fin d) : Fin n → Bool × Fin d := fun j => (b j, z j)

def Pbb {n : ℕ} (b : Fin n → Bool) (P : Matrix (Fin n → Bool × Fin d) (Fin n → Bool × Fin d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ := Matrix.of fun z z' => P (pairL b z) (pairL b z')

lemma Pbb_psd {n : ℕ} (b : Fin n → Bool) {P : Matrix (Fin n → Bool × Fin d) (Fin n → Bool × Fin d) ℂ}
    (hP : P.PosSemidef) : (Pbb b P).PosSemidef := by
  have := hP.submatrix (pairL b)
  exact this

lemma Pbb_one {n : ℕ} (b : Fin n → Bool) : Pbb b (1 : Matrix (Fin n → Bool × Fin d) _ ℂ) = 1 := by
  ext z z'
  simp only [Pbb, Matrix.of_apply, Matrix.one_apply]
  by_cases h : z = z'
  · subst h; simp
  · rw [if_neg, if_neg h]
    intro h2; apply h; funext j; have := congrFun h2 j; simp [pairL] at this; exact this

lemma label_trace {n : ℕ} (P : Matrix (Fin n → Bool × Fin d) (Fin n → Bool × Fin d) ℂ) (ρ σ : Mat d) :
    (P * powerState (labelledState ρ σ) n).trace =
      ∑ b : Fin n → Bool, ((2:ℂ)⁻¹)^n * (Pbb b P * Tl ρ σ b).trace := by
  set e := (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Bool) (fun _ => Fin d)).symm
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [← e.sum_comp]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [← e.sum_comp, ← Finset.univ_product_univ, Finset.sum_product]
  rw [Finset.sum_eq_single b]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z' _ => ?_)
    simp only [powerState, tensor, OptimalSpectrum.Entangled.kronFamily, Matrix.of_apply, labelledState,
      Pbb, Tl, e, Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk, pairL]
    simp only [if_true, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have : ∀ j, (if b j = true then σ (z' j) (z j) else ρ (z' j) (z j)) = tauB ρ σ (b j) (z' j) (z j) := by
      intro j; cases b j <;> rfl
    simp only [this]
    rw [show pairL b z = fun c => (b c, z c) from rfl, show pairL b z' = fun c => (b c, z' c) from rfl]
    ring
  · intro b' _ hb'
    refine Finset.sum_eq_zero (fun z' _ => ?_)
    simp only [powerState, tensor, OptimalSpectrum.Entangled.kronFamily, Matrix.of_apply, labelledState,
      e, Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]
    obtain ⟨j, hj⟩ : ∃ j, b' j ≠ b j := by
      by_contra h; push_neg at h; exact hb' (funext h)
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), mul_zero]
  · simp


/-! ### finite cells of unitaries -/

def cellBound (η : ℝ) : ℤ := (⌈1/η⌉₊ : ℤ) + 1

def CellSet (d : ℕ) (η : ℝ) : Finset (Fin d → Fin d → ℤ × ℤ) :=
  Fintype.piFinset (fun _ => Fintype.piFinset (fun _ =>
    Finset.Icc (-cellBound η) (cellBound η) ×ˢ Finset.Icc (-cellBound η) (cellBound η)))

lemma floor_mem {η x : ℝ} (hη : 0 < η) (hx : |x| ≤ 1) :
    ⌊x / η⌋ ∈ Finset.Icc (-cellBound η) (cellBound η) := by
  rw [Finset.mem_Icc, cellBound]
  have hc : 1/η ≤ (⌈1/η⌉₊ : ℝ) := Nat.le_ceil _
  rw [abs_le] at hx
  constructor
  · have h1 : -(1/η) ≤ x / η := by
      rw [neg_le, ← neg_div]; exact div_le_div_of_nonneg_right (by linarith) hη.le
    have h2 : (-(⌈1/η⌉₊ : ℤ) - 1 : ℝ) < ⌊x/η⌋ := by
      have := Int.sub_one_lt_floor (x/η); push_cast; linarith
    have : (-(⌈1/η⌉₊ : ℤ) - 1 : ℤ) < ⌊x/η⌋ := by exact_mod_cast h2
    omega
  · have h1 : x / η ≤ 1/η := div_le_div_of_nonneg_right hx.2 hη.le
    have h2 : (⌊x/η⌋ : ℝ) ≤ ⌈1/η⌉₊ := (Int.floor_le _).trans (h1.trans hc)
    have : ⌊x/η⌋ ≤ (⌈1/η⌉₊ : ℤ) := by exact_mod_cast h2
    omega

lemma gridCell_mem {η : ℝ} (hη : 0 < η) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    gridCell η (U : Mat d) ∈ CellSet d η := by
  simp only [CellSet, Fintype.mem_piFinset, Finset.mem_product]
  intro i j
  have hb := entry_norm_bound_of_unitary U.2 i j
  refine ⟨floor_mem hη ?_, floor_mem hη ?_⟩
  · exact (Complex.abs_re_le_norm _).trans hb
  · exact (Complex.abs_im_le_norm _).trans hb

abbrev Cells (d : ℕ) (η : ℝ) := ↥(CellSet d η)

/-- the measurable cell of an outcome -/
def Sset {m : ℕ} (η : ℝ) (t : QAlgorithms.Schur.Partition d m × Cells d η) :
    Set (QAlgorithms.Schur.Partition d m × Matrix.unitaryGroup (Fin d) ℂ) :=
  {o | o.1 = t.1 ∧ gridCell η (o.2 : Mat d) = t.2.1}

set_option backward.isDefEq.respectTransparency.types false in
open scoped Matrix.Norms.Elementwise in
lemma measurable_gridCell_eq (η : ℝ) (k : Fin d → Fin d → ℤ × ℤ) :
    MeasurableSet {U : Matrix.unitaryGroup (Fin d) ℂ | gridCell η (U : Mat d) = k} := by
  have hset : {U : Matrix.unitaryGroup (Fin d) ℂ | gridCell η (U : Mat d) = k} =
      ⋂ i, ⋂ j, ({U : Matrix.unitaryGroup (Fin d) ℂ | ⌊((U : Mat d) i j).re / η⌋ = (k i j).1} ∩
        {U | ⌊((U : Mat d) i j).im / η⌋ = (k i j).2}) := by
    ext U
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, gridCell]
    constructor
    · intro h i j; rw [← h]; exact ⟨rfl, rfl⟩
    · intro h; funext i j; exact Prod.ext (h i j).1 (h i j).2
  rw [hset]
  refine MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j => MeasurableSet.inter ?_ ?_))
  · have hc : Continuous fun U : Matrix.unitaryGroup (Fin d) ℂ => ((U : Mat d) i j).re / η :=
      (Complex.continuous_re.comp ((continuous_apply j).comp ((continuous_apply i).comp
        continuous_subtype_val))).div_const η
    exact (Int.measurable_floor.comp hc.measurable) (measurableSet_singleton _)
  · have hc : Continuous fun U : Matrix.unitaryGroup (Fin d) ℂ => ((U : Mat d) i j).im / η :=
      (Complex.continuous_im.comp ((continuous_apply j).comp ((continuous_apply i).comp
        continuous_subtype_val))).div_const η
    exact (Int.measurable_floor.comp hc.measurable) (measurableSet_singleton _)

lemma Sset_measurable {m : ℕ} (η : ℝ) (t : QAlgorithms.Schur.Partition d m × Cells d η) :
    MeasurableSet (Sset η t) := by
  have : Sset η t = (Prod.fst ⁻¹' {t.1}) ∩
      (Prod.snd ⁻¹' {U : Matrix.unitaryGroup (Fin d) ℂ | gridCell η (U : Mat d) = t.2.1}) := by
    ext o; simp [Sset]
  rw [this]
  exact (measurable_fst (measurableSet_singleton _)).inter
    (measurable_snd (measurable_gridCell_eq η t.2.1))

lemma Sset_disjoint {m : ℕ} (η : ℝ) {t t' : QAlgorithms.Schur.Partition d m × Cells d η} (h : t ≠ t') :
    Disjoint (Sset η t) (Sset η t') := by
  rw [Set.disjoint_left]
  intro o ho ho'
  apply h
  obtain ⟨h1, h2⟩ := ho
  obtain ⟨h1', h2'⟩ := ho'
  exact Prod.ext (h1.symm.trans h1') (Subtype.ext (h2.symm.trans h2'))

def cellOf {m : ℕ} {η : ℝ} (hη : 0 < η) (o : QAlgorithms.Schur.Partition d m × Matrix.unitaryGroup (Fin d) ℂ) :
    QAlgorithms.Schur.Partition d m × Cells d η := (o.1, ⟨gridCell η (o.2 : Mat d), gridCell_mem hη o.2⟩)

lemma mem_Sset_iff {m : ℕ} {η : ℝ} (hη : 0 < η) (o : QAlgorithms.Schur.Partition d m × Matrix.unitaryGroup (Fin d) ℂ)
    (t : QAlgorithms.Schur.Partition d m × Cells d η) : o ∈ Sset η t ↔ cellOf hη o = t := by
  constructor
  · rintro ⟨h1, h2⟩; exact Prod.ext h1 (Subtype.ext h2)
  · intro h; rw [← h]; exact ⟨rfl, rfl⟩

lemma iUnion_Sset {m : ℕ} {η : ℝ} (hη : 0 < η) :
    (⋃ t ∈ (Finset.univ : Finset (QAlgorithms.Schur.Partition d m × Cells d η)), Sset η t) = Set.univ := by
  ext o; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨cellOf hη o, Finset.mem_univ _, (mem_Sset_iff hη o _).2 rfl⟩

/-! ### finite additivity of an operator POVM -/

section povm
variable {I O : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace O]

lemma povm_union (E : QAlgorithms.Measurements.OperatorPOVM I O) {A B : Set O}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) :
    E.operator (A ∪ B) = E.operator A + E.operator B := by
  set S : ℕ → Set O := fun i => if i = 0 then A else if i = 1 then B else ∅ with hS
  have hm : ∀ i, MeasurableSet (S i) := by
    intro i; simp only [hS]; split_ifs <;> first | exact hA | exact hB | exact MeasurableSet.empty
  have hd : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    simp only [hS]
    split_ifs <;> first | (exfalso; omega) | exact hAB | exact hAB.symm | simp
  have h := E.additive S hm hd
  have hU : (⋃ i, S i) = A ∪ B := by
    ext x; simp only [Set.mem_iUnion, Set.mem_union, hS]
    constructor
    · rintro ⟨i, hi⟩; split_ifs at hi with h0 h1
      · exact Or.inl hi
      · exact Or.inr hi
      · exact absurd hi (Set.notMem_empty x)
    · rintro (h | h)
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
  rw [hU] at h
  have h2 : HasSum (fun i => E.operator (S i)) (E.operator A + E.operator B) := by
    have h3 : HasSum (fun i => E.operator (S i)) (∑ i ∈ ({0, 1} : Finset ℕ), E.operator (S i)) := by
      refine hasSum_sum_of_ne_finset_zero (fun i hi => ?_)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      simp [hS, hi.1, hi.2, E.empty]
    rw [Finset.sum_pair (by norm_num)] at h3
    simpa [hS] using h3
  exact h.unique h2

lemma povm_finset {ι : Type*} [DecidableEq ι] (E : QAlgorithms.Measurements.OperatorPOVM I O)
    (s : Finset ι) (S : ι → Set O) (hm : ∀ i, MeasurableSet (S i))
    (hd : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    E.operator (⋃ i ∈ s, S i) = ∑ i ∈ s, E.operator (S i) := by
  induction s using Finset.induction_on with
  | empty => simp [E.empty]
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, povm_union E (hm a) (Finset.measurableSet_biUnion s (fun i _ => hm i)),
      ih, Finset.sum_insert ha]
    rw [Set.disjoint_iUnion₂_right]
    intro i hi; exact hd a i (fun h => ha (h ▸ hi))

end povm


/-! ### copied facts -/

lemma kron_mul {ι : Type*} [Fintype ι] {r : ℕ} (A B : Fin r → Matrix ι ι ℂ) :
    OptimalSpectrum.Entangled.kronFamily (fun j => A j * B j) =
      OptimalSpectrum.Entangled.kronFamily A * OptimalSpectrum.Entangled.kronFamily B := by
  ext x y
  simp only [OptimalSpectrum.Entangled.kronFamily, mul_apply, Matrix.of_apply]
  have := Fintype.prod_sum (fun (j : Fin r) (c : ι) => A j (x j) c * B j c (y j))
  rw [this]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.prod_mul_distrib]

lemma kron_conj {ι : Type*} [Fintype ι] {r : ℕ} (A : Fin r → Matrix ι ι ℂ) :
    (OptimalSpectrum.Entangled.kronFamily A)ᴴ =
      OptimalSpectrum.Entangled.kronFamily (fun j => (A j)ᴴ) := by
  ext x y
  simp [OptimalSpectrum.Entangled.kronFamily, conjTranspose_apply, star_prod]

lemma powerState_psd {ι : Type*} [Fintype ι] [DecidableEq ι] {τ : Matrix ι ι ℂ} (hτ : τ.PosSemidef)
    (n : ℕ) : (powerState τ n).PosSemidef := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hτ.nonneg
  have : powerState τ n = (OptimalSpectrum.Entangled.kronFamily (fun _ : Fin n => B))ᴴ *
      OptimalSpectrum.Entangled.kronFamily (fun _ : Fin n => B) := by
    rw [kron_conj, ← kron_mul]
    simp only [powerState, tensor, hB, Matrix.star_eq_conjTranspose]
  rw [this]; exact posSemidef_conjTranspose_mul_self _

lemma labelled_psd {d : ℕ} {ρ σ : Mat d} (hρ : Density ρ) (hσ : Density σ) :
    (labelledState ρ σ).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
  · ext ⟨b, i⟩ ⟨b', j⟩
    simp only [labelledState, conjTranspose_apply]
    by_cases h : b' = b
    · subst h
      simp only [if_true]
      cases b'
      · simp only [Bool.false_eq_true, if_false, star_mul', star_inv₀, star_ofNat]
        rw [show star (ρ j i) = ρ i j from by
          have := congrFun (congrFun hρ.1.1 i) j; simpa [conjTranspose_apply] using this]
      · simp only [if_true, star_mul', star_inv₀, star_ofNat]
        rw [show star (σ j i) = σ i j from by
          have := congrFun (congrFun hσ.1.1 i) j; simpa [conjTranspose_apply] using this]
    · rw [if_neg h, if_neg (Ne.symm h)]; simp
  · set u : Fin d → ℂ := fun i => x (false, i)
    set w : Fin d → ℂ := fun i => x (true, i)
    have e : star x ⬝ᵥ (labelledState ρ σ *ᵥ x) =
        (2:ℂ)⁻¹ * (star u ⬝ᵥ (ρ *ᵥ u)) + (2:ℂ)⁻¹ * (star w ⬝ᵥ (σ *ᵥ w)) := by
      simp only [dotProduct, mulVec, labelledState, Fintype.sum_prod_type, Fintype.sum_bool,
        Pi.star_apply, u, w]
      simp [Finset.mul_sum, Finset.sum_add_distrib, mul_comm, mul_left_comm, mul_assoc]
      ring_nf
    rw [e]
    have h2 : (0:ℂ) ≤ (2:ℂ)⁻¹ := by
      rw [show (2:ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; rfl]; exact_mod_cast (by norm_num : (0:ℝ) ≤ 2⁻¹)
    exact add_nonneg (mul_nonneg h2 (hρ.1.dotProduct_mulVec_nonneg u))
      (mul_nonneg h2 (hσ.1.dotProduct_mulVec_nonneg w))



lemma herm_smul_real' {ι : Type*} [Fintype ι] (c : ℝ) {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    ((c : ℂ) • A).IsHermitian := by
  unfold IsHermitian at hA ⊢; rw [conjTranspose_smul, hA]; simp [Complex.conj_ofReal]


lemma herm_finsum {ι κ : Type*} [Fintype ι] (S : Finset κ) (A : κ → Matrix ι ι ℂ)
    (h : ∀ k ∈ S, (A k).IsHermitian) : (∑ k ∈ S, A k).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_sum]
  exact Finset.sum_congr rfl (fun k hk => h k hk)

lemma embed_herm {ι : Type*} [Fintype ι] [DecidableEq ι] {k n : ℕ} (e : Fin k ↪ Fin n)
    {H : Matrix (Fin k → ι) (Fin k → ι) ℂ} (hH : H.IsHermitian) : (embed e H).IsHermitian := by
  ext x y
  simp only [conjTranspose_apply, embed]
  have hc : (∀ i, i ∉ Set.range e → y i = x i) ↔ (∀ i, i ∉ Set.range e → x i = y i) :=
    ⟨fun h i hi => (h i hi).symm, fun h i hi => (h i hi).symm⟩
  by_cases h : ∀ i, i ∉ Set.range e → x i = y i
  · rw [if_pos (hc.mpr h), if_pos h]
    have := congrFun (congrFun hH (x ∘ e)) (y ∘ e)
    simpa [conjTranspose_apply] using this
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h, star_zero]

lemma uStat_herm {ι : Type*} [Fintype ι] [DecidableEq ι] (n k : ℕ)
    {H : Matrix (Fin k → ι) (Fin k → ι) ℂ} (hH : H.IsHermitian) : (uStatistic n k H).IsHermitian := by
  unfold uStatistic
  have hs : (∑ e : Fin k ↪ Fin n, embed e H).IsHermitian :=
    herm_finsum _ _ (fun e _ => embed_herm e hH)
  unfold IsHermitian at hs ⊢
  rw [conjTranspose_smul, hs]; congr 1; simp

lemma hermPart_herm {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : (hermPart A).IsHermitian := by
  unfold hermPart IsHermitian
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]; simp

lemma obs_herm (g : TraceExpression d) (n : ℕ) : (observable g n).IsHermitian := by
  unfold observable
  refine IsHermitian.add ?_ (herm_finsum _ _ (fun k _ => uStat_herm n k (hermPart_herm _)))
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact herm_smul_real' _ isHermitian_one



lemma pure_psd {ι : Type*} [Fintype ι] [DecidableEq ι] (v : EuclideanSpace ℂ ι) :
    (QAlgorithms.pureDensity v).PosSemidef := by
  have : QAlgorithms.pureDensity v = Matrix.vecMulVec (fun a => v a) (star (fun a => v a)) := by
    ext a b; simp [QAlgorithms.pureDensity, Matrix.vecMulVec_apply]
  rw [this]
  exact Matrix.posSemidef_vecMulVec_self_star _

/-! ### the rounded law is a finite sum of point masses -/

section finlaw
variable {m : ℕ} (hd : 0 < d) (hm : 0 < m) {η : ℝ} (hη : 0 < η)

def rep (t : QAlgorithms.Schur.Partition d m × Cells d η) : Mat d :=
  QAlgorithms.Schur.estimate hd hm t.1 (cellUnitary η t.2.1)

include hη in
lemma rest_measurable :
    Measurable (fun o : QAlgorithms.Schur.Partition d m × Matrix.unitaryGroup (Fin d) ℂ =>
      QAlgorithms.Schur.estimate hd hm o.1 (roundUnitary η o.2)) := by
  intro S _
  have hset : (fun o : QAlgorithms.Schur.Partition d m × Matrix.unitaryGroup (Fin d) ℂ =>
      QAlgorithms.Schur.estimate hd hm o.1 (roundUnitary η o.2)) ⁻¹' S =
      ⋃ t ∈ (Finset.univ.filter (fun t => rep hd hm t ∈ S)), Sset η t := by
    ext o
    simp only [Set.mem_preimage, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨cellOf hη o, h, (mem_Sset_iff hη o _).2 rfl⟩
    · rintro ⟨t, ht, ho⟩
      rw [mem_Sset_iff hη] at ho; rw [← ho] at ht; exact ht
  rw [hset]
  exact Finset.measurableSet_biUnion _ (fun t _ => Sset_measurable η t)

include hη in
lemma map_eq (μ : Measure (QAlgorithms.Schur.Partition d m × Matrix.unitaryGroup (Fin d) ℂ)) :
    Measure.map (fun o => QAlgorithms.Schur.estimate hd hm o.1 (roundUnitary η o.2)) μ =
      ∑ t : QAlgorithms.Schur.Partition d m × Cells d η, μ (Sset η t) • Measure.dirac (rep hd hm t) := by
  ext S hS
  rw [Measure.map_apply (rest_measurable hd hm hη) hS, Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hS, smul_eq_mul]
  have hset : (fun o : QAlgorithms.Schur.Partition d m × Matrix.unitaryGroup (Fin d) ℂ =>
      QAlgorithms.Schur.estimate hd hm o.1 (roundUnitary η o.2)) ⁻¹' S =
      ⋃ t ∈ (Finset.univ.filter (fun t => rep hd hm t ∈ S)), Sset η t := by
    ext o
    simp only [Set.mem_preimage, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨cellOf hη o, h, (mem_Sset_iff hη o _).2 rfl⟩
    · rintro ⟨t, ht, ho⟩
      rw [mem_Sset_iff hη] at ho; rw [← ho] at ht; exact ht
  rw [hset, measure_biUnion_finset (fun t _ t' _ h => Sset_disjoint η h) (fun t _ => Sset_measurable η t),
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  by_cases h : rep hd hm t ∈ S
  · rw [if_pos h, Set.indicator_of_mem h]; simp
  · rw [if_neg h, Set.indicator_of_notMem h]; simp

end finlaw

/-! ### spectral projectors -/

section spec
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def specProj {G : Matrix ι ι ℂ} (hG : G.IsHermitian) (S : Set ℝ) : Matrix ι ι ℂ :=
  ∑ i, if hG.eigenvalues i ∈ S then QAlgorithms.pureDensity (hG.eigenvectorBasis i) else 0

lemma specProj_empty {G : Matrix ι ι ℂ} (hG : G.IsHermitian) : specProj hG ∅ = 0 := by
  simp [specProj]

lemma specProj_univ {G : Matrix ι ι ℂ} (hG : G.IsHermitian) : specProj hG Set.univ = 1 := by
  simp only [specProj, Set.mem_univ, if_true]
  have hU : (hG.eigenvectorUnitary : Matrix ι ι ℂ) * star (hG.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
    Unitary.mul_star_self_of_mem hG.eigenvectorUnitary.2
  rw [← hU]
  ext a b
  simp only [Matrix.sum_apply, QAlgorithms.pureDensity, Matrix.of_apply, Matrix.mul_apply, Matrix.star_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply]
  rfl

lemma specProj_psd {G : Matrix ι ι ℂ} (hG : G.IsHermitian) (S : Set ℝ) : (specProj hG S).PosSemidef := by
  unfold specProj
  refine Finset.sum_induction _ (fun M : Matrix ι ι ℂ => M.PosSemidef) (fun a b ha hb => ha.add hb)
    PosSemidef.zero (fun i _ => ?_)
  split_ifs
  · exact pure_psd _
  · exact PosSemidef.zero

lemma specProj_hasSum {G : Matrix ι ι ℂ} (hG : G.IsHermitian) (S : ℕ → Set ℝ)
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) :
    HasSum (fun k => specProj hG (S k)) (specProj hG (⋃ k, S k)) := by
  unfold specProj
  refine hasSum_sum (fun i _ => ?_)
  by_cases h : ∃ k, hG.eigenvalues i ∈ S k
  · obtain ⟨k0, hk0⟩ := h
    have huniq : ∀ k, k ≠ k0 → hG.eigenvalues i ∉ S k := by
      intro k hk hin
      exact Set.disjoint_left.1 (hd hk) hin hk0
    rw [if_pos (Set.mem_iUnion.2 ⟨k0, hk0⟩)]
    convert hasSum_ite_eq k0 (QAlgorithms.pureDensity (hG.eigenvectorBasis i)) using 1
    funext k
    by_cases hk : k = k0
    · subst hk; simp [hk0]
    · rw [if_neg (huniq k hk), if_neg hk]
  · push_neg at h
    rw [if_neg (by simp only [Set.mem_iUnion, not_exists]; exact h)]
    convert hasSum_zero using 1
    funext k; rw [if_neg (h k)]

lemma spectralLaw_eval {G R : Matrix ι ι ℂ} (hG : G.IsHermitian) (hR : R.PosSemidef) {S : Set ℝ}
    (hS : MeasurableSet S) :
    spectralLaw G R S = ENNReal.ofReal (QAlgorithms.effectProb (specProj hG S) R) := by
  unfold spectralLaw
  rw [dif_pos hG, Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hS, smul_eq_mul]
  unfold QAlgorithms.effectProb specProj
  rw [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => ?_)]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : hG.eigenvalues i ∈ S
    · rw [Set.indicator_of_mem h, if_pos h, Pi.one_apply, mul_one, tr, Matrix.trace_mul_comm]
    · rw [Set.indicator_of_notMem h, if_neg h, mul_zero, Matrix.zero_mul, Matrix.trace_zero,
        Complex.zero_re, ENNReal.ofReal_zero]
  · split_ifs
    · exact QAlgorithms.Measurements.born_nonnegative (pure_psd _) hR
    · simp

end spec

/-! ### generic helpers for the composite measurements -/

lemma sum_kron_sum {ι κ α β : Type*} (s : Finset ι) (t : Finset κ) [Fintype α] [Fintype β]
    (A : ι → Matrix α α ℂ) (B : κ → Matrix β β ℂ) :
    (∑ i ∈ s, A i) ⊗ₖ (∑ j ∈ t, B j) = ∑ i ∈ s, ∑ j ∈ t, A i ⊗ₖ B j := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul_sum]

lemma trace_herm_mul_im {ι : Type*} [Fintype ι] {A B : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) : (A * B).trace.im = 0 := by
  have h : star (A * B).trace = (A * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq, Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_im.1 h

lemma trace_eq_ofReal {ι : Type*} [Fintype ι] {A B : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) : (A * B).trace = (((A * B).trace.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [trace_herm_mul_im hA hB]

lemma ite_hasSum {X : Type*} [AddCommMonoid X] [TopologicalSpace X] (x : ℝ) (M : X) (S : ℕ → Set ℝ)
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) :
    HasSum (fun k => if x ∈ S k then M else 0) (if x ∈ ⋃ k, S k then M else 0) := by
  by_cases h : ∃ k, x ∈ S k
  · obtain ⟨k0, hk0⟩ := h
    rw [if_pos (Set.mem_iUnion.2 ⟨k0, hk0⟩)]
    convert hasSum_ite_eq k0 M using 1
    funext k
    by_cases hk : k = k0
    · subst hk; simp [hk0]
    · rw [if_neg (fun hin => Set.disjoint_left.1 (hd hk) hin hk0), if_neg hk]
  · push_neg at h
    rw [if_neg (by simp only [Set.mem_iUnion, not_exists]; exact h)]
    convert hasSum_zero using 1
    funext k; rw [if_neg (h k)]

lemma lintegral_fin_dirac {T : Type*} [Fintype T] (c : T → ℝ≥0∞) (x : T → Mat d) (g : Mat d → ℝ≥0∞) :
    ∫⁻ a, g a ∂(∑ t, c t • Measure.dirac (x t)) = ∑ t, c t * g (x t) := by
  rw [lintegral_finset_sum_measure]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-! ### the bounded branch -/

theorem bounded_real (m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    ∃ M : TwoStateMeasurement d m, ∀ (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ) (B : Set ℝ),
      MeasurableSet B → outcomeLaw M ρ σ hρ hσ B =
        ∫⁻ a : Mat d, ∫⁻ b : Mat d, (if distance a b ∈ B then 1 else 0)
          ∂roundedTomographyLaw m σ hσ ∂roundedTomographyLaw m ρ hρ := by
  obtain ⟨E, hE⟩ := QAlgorithms.Papers.RoadmapL03.keyl_expectedSquaredFrobeniusError d m hd hm
  set η := roundingMesh d m with hηdef
  have hη : 0 < η := by rw [hηdef, roundingMesh]; positivity
  set F : QAlgorithms.Schur.Partition d m × Cells d η → Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ :=
    fun t => E.operator (Sset η t) with hF
  have hFpsd : ∀ t, (F t).PosSemidef := fun t => E.positive _ (Sset_measurable η t)
  have hFsum : ∑ t, F t = 1 := by
    rw [hF, ← povm_finset E Finset.univ (Sset η) (Sset_measurable η) (fun i j h => Sset_disjoint η h),
      iUnion_Sset hη, E.total]
  set R := rep (d := d) hd hm (η := η) with hR
  let op : Set ℝ → Matrix (Register d m × Register d m) (Register d m × Register d m) ℂ := fun B =>
    ∑ t1, ∑ t2, if distance (R t1) (R t2) ∈ B then F t1 ⊗ₖ F t2 else 0
  let M : TwoStateMeasurement d m :=
    { operator := op
      empty := by simp [op]
      total := by
        simp only [op, Set.mem_univ, if_true]
        rw [← sum_kron_sum, hFsum, Matrix.one_kronecker_one]
      positive := by
        intro B _
        refine Finset.sum_induction _ (fun M : Matrix _ _ ℂ => M.PosSemidef) (fun a b ha hb => ha.add hb)
          PosSemidef.zero (fun t1 _ => ?_)
        refine Finset.sum_induction _ (fun M : Matrix _ _ ℂ => M.PosSemidef) (fun a b ha hb => ha.add hb)
          PosSemidef.zero (fun t2 _ => ?_)
        split_ifs
        · exact (hFpsd t1).kronecker (hFpsd t2)
        · exact PosSemidef.zero
      additive := by
        intro B _ hd'
        exact hasSum_sum (fun t1 _ => hasSum_sum (fun t2 _ => ite_hasSum _ _ B hd')) }
  refine ⟨M, fun ρ σ hρ hσ B hB => ?_⟩
  -- the Keyl laws are finite sums
  have hlaw : ∀ (τ : Mat d) (hτ : Density τ), roundedTomographyLaw m τ hτ =
      ∑ t, ENNReal.ofReal (QAlgorithms.effectProb (F t) (QAlgorithms.piKron m τ)) • Measure.dirac (R t) := by
    intro τ hτ
    rw [roundedTomographyLaw, dif_pos ⟨hd, hm⟩, map_eq hd hm hη]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [← (hE τ hτ).1, QAlgorithms.Measurements.bornLaw_apply _ _ _ _ (Sset_measurable η t)]
  rw [hlaw ρ hρ, lintegral_fin_dirac]
  simp only [hlaw σ hσ, lintegral_fin_dirac]
  -- the left side
  unfold outcomeLaw
  rw [QAlgorithms.Measurements.bornLaw_apply _ _ _ _ hB]
  have hP : ∀ (τ : Mat d), Density τ → (QAlgorithms.piKron m τ).IsHermitian := fun τ hτ =>
    (QAlgorithms.Tomography.tensorDensity τ hτ m).1.1
  have hnn : ∀ t (τ : Mat d), Density τ → 0 ≤ QAlgorithms.effectProb (F t) (QAlgorithms.piKron m τ) :=
    fun t τ hτ => QAlgorithms.Measurements.born_nonnegative (hFpsd t) (QAlgorithms.Tomography.tensorDensity τ hτ m).1
  have hEP : QAlgorithms.effectProb (op B) (jointInput m ρ σ) =
      ∑ t1, ∑ t2, (if distance (R t1) (R t2) ∈ B then 1 else 0) *
        (QAlgorithms.effectProb (F t1) (QAlgorithms.piKron m ρ) *
          QAlgorithms.effectProb (F t2) (QAlgorithms.piKron m σ)) := by
    unfold QAlgorithms.effectProb
    simp only [op, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun t1 _ => Finset.sum_congr rfl (fun t2 _ => ?_))
    split_ifs
    · rw [one_mul, show jointInput m ρ σ = QAlgorithms.piKron m ρ ⊗ₖ QAlgorithms.piKron m σ from rfl,
        ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,
        trace_eq_ofReal (hFpsd t1).1 (hP ρ hρ), trace_eq_ofReal (hFpsd t2).1 (hP σ hσ)]
      simp only [Complex.ofReal_re]
      rw [← Complex.ofReal_mul, Complex.ofReal_re]
    · simp
  rw [hEP, ENNReal.ofReal_sum_of_nonneg (fun t1 _ => Finset.sum_nonneg (fun t2 _ => by
    split_ifs <;> positivity [hnn t1 ρ hρ, hnn t2 σ hσ]))]
  refine Finset.sum_congr rfl (fun t1 _ => ?_)
  rw [ENNReal.ofReal_sum_of_nonneg (fun t2 _ => by split_ifs <;> positivity [hnn t1 ρ hρ, hnn t2 σ hσ]),
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t2 _ => ?_)
  split_ifs
  · rw [one_mul, ENNReal.ofReal_mul (hnn t1 ρ hρ), mul_one]
  · simp

/-! ### the main branch -/

def eqvR (m n : ℕ) : Register d (m+n) × Register d (m+n) ≃ (Fin m → D2 d) × (Fin n → D2 d) where
  toFun xy := (fun k => (xy.1 (Fin.castAdd n k), xy.2 (Fin.castAdd n k)),
    fun j => (xy.1 (Fin.natAdd m j), xy.2 (Fin.natAdd m j)))
  invFun pq := (Fin.append (fun k => (pq.1 k).1) (fun j => (pq.2 j).1),
    Fin.append (fun k => (pq.1 k).2) (fun j => (pq.2 j).2))
  left_inv xy := by
    obtain ⟨x, y⟩ := xy
    simp only [Prod.mk.injEq]
    exact ⟨Fin.append_castAdd_natAdd, Fin.append_castAdd_natAdd⟩
  right_inv pq := by
    obtain ⟨p, q⟩ := pq
    simp only [Fin.append_left, Fin.append_right]

lemma jointInput_eq (m n : ℕ) (ρ σ : Mat d) :
    jointInput (m+n) ρ σ = (QAlgorithms.piKron m (pairState ρ σ) ⊗ₖ
      QAlgorithms.piKron n (pairState ρ σ)).submatrix (eqvR m n) (eqvR m n) := by
  ext ⟨x, y⟩ ⟨x', y'⟩
  simp only [jointInput, Matrix.kronecker, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    QAlgorithms.piKron, Matrix.of_apply, eqvR, Equiv.coe_fn_mk, pairState]
  rw [Fin.prod_univ_add, Fin.prod_univ_add, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

def Emb1 {m : ℕ} (A : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) : Matrix (Fin m → D2 d) (Fin m → D2 d) ℂ :=
  ∑ l : Fin m → Bool, ((2:ℂ)⁻¹)^m • Emb l A

def Emb2 {n : ℕ} (P : Matrix (Fin n → Bool × Fin d) (Fin n → Bool × Fin d) ℂ) :
    Matrix (Fin n → D2 d) (Fin n → D2 d) ℂ :=
  ∑ b : Fin n → Bool, ((2:ℂ)⁻¹)^n • Emb b (Pbb b P)

lemma half_pow_sum (k : ℕ) : ∑ _b : Fin k → Bool, ((2:ℂ)⁻¹)^k = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul]; push_cast; rw [← mul_pow]; norm_num

lemma Emb1_one {m : ℕ} : Emb1 (d := d) (1 : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) = 1 := by
  unfold Emb1; simp only [Emb_one, ← Finset.sum_smul, half_pow_sum, one_smul]

lemma Emb2_one {n : ℕ} : Emb2 (d := d) (1 : Matrix (Fin n → Bool × Fin d) _ ℂ) = 1 := by
  unfold Emb2; simp only [Pbb_one, Emb_one, ← Finset.sum_smul, half_pow_sum, one_smul]

lemma Pbb_zero {n : ℕ} (b : Fin n → Bool) : Pbb b (0 : Matrix (Fin n → Bool × Fin d) _ ℂ) = 0 := by
  ext; simp [Pbb]

lemma Emb2_zero {n : ℕ} : Emb2 (d := d) (0 : Matrix (Fin n → Bool × Fin d) _ ℂ) = 0 := by
  unfold Emb2; simp [Pbb_zero, Emb_zero]

lemma Emb1_sum {m : ℕ} {T : Type*} [Fintype T] (A : T → Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) :
    Emb1 (∑ t, A t) = ∑ t, Emb1 (A t) := by
  unfold Emb1
  have : ∀ l : Fin m → Bool, Emb l (∑ t, A t) = ∑ t, Emb l (A t) := by
    intro l
    induction (Finset.univ : Finset T) using Finset.induction_on with
    | empty => simp [Emb_zero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Emb_add, ih, Finset.sum_insert ha]
  simp only [this, Finset.smul_sum]
  rw [Finset.sum_comm]

lemma half_nonneg (k : ℕ) : (0:ℂ) ≤ ((2:ℂ)⁻¹)^k := by
  have : ((2:ℂ)⁻¹)^k = (((2:ℝ)⁻¹)^k : ℝ) := by push_cast; rfl
  rw [this]; exact_mod_cast (by positivity : (0:ℝ) ≤ ((2:ℝ)⁻¹)^k)

lemma Emb1_psd {m : ℕ} {A : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ} (hA : A.PosSemidef) :
    (Emb1 A).PosSemidef := by
  unfold Emb1
  refine Finset.sum_induction _ (fun M : Matrix _ _ ℂ => M.PosSemidef) (fun a b ha hb => ha.add hb)
    PosSemidef.zero (fun l _ => (Emb_psd l hA).smul (half_nonneg m))

lemma Emb2_psd {n : ℕ} {P : Matrix (Fin n → Bool × Fin d) _ ℂ} (hP : P.PosSemidef) :
    (Emb2 P).PosSemidef := by
  unfold Emb2
  refine Finset.sum_induction _ (fun M : Matrix _ _ ℂ => M.PosSemidef) (fun a b ha hb => ha.add hb)
    PosSemidef.zero (fun b _ => (Emb_psd b (Pbb_psd b hP)).smul (half_nonneg n))

lemma Emb1_trace {m : ℕ} (A : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) {ρ σ : Mat d}
    (hρ : ρ.trace = 1) (hσ : σ.trace = 1) :
    (Emb1 A * QAlgorithms.piKron m (pairState ρ σ)).trace = (A * QAlgorithms.piKron m (plus ρ σ)).trace := by
  rw [mixture_trace A hρ hσ, Emb1, Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

lemma Emb2_trace {n : ℕ} (P : Matrix (Fin n → Bool × Fin d) _ ℂ) {ρ σ : Mat d}
    (hρ : ρ.trace = 1) (hσ : σ.trace = 1) :
    (Emb2 P * QAlgorithms.piKron n (pairState ρ σ)).trace = (P * powerState (labelledState ρ σ) n).trace := by
  rw [label_trace, Emb2, Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Emb_trace b _ hρ hσ]

lemma trace_sub_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : κ ≃ ι) (X Y : Matrix ι ι ℂ) : (X.submatrix e e * Y.submatrix e e).trace = (X * Y).trace := by
  rw [Matrix.submatrix_mul_equiv X Y e e e]
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun i => (X * Y) i i)

theorem main_real (m n : ℕ) (hd : 0 < d) (hm : 0 < m)
    (G : Mat d → Matrix (Fin n → Bool × Fin d) (Fin n → Bool × Fin d) ℂ) (hG : ∀ r, (G r).IsHermitian)
    (g : ℝ → ℝ) (hg : Measurable g) :
    ∃ M : TwoStateMeasurement d (m + n), ∀ (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ)
      (hP : Density (plus ρ σ)) (B : Set ℝ), MeasurableSet B →
        outcomeLaw M ρ σ hρ hσ B =
          ∫⁻ report, spectralLaw (G report) (powerState (labelledState ρ σ) n) (g ⁻¹' B)
            ∂roundedTomographyLaw m (plus ρ σ) hP := by
  obtain ⟨E, hE⟩ := QAlgorithms.Papers.RoadmapL03.keyl_expectedSquaredFrobeniusError d m hd hm
  set η := roundingMesh d m with hηdef
  have hη : 0 < η := by rw [hηdef, roundingMesh]; positivity
  set F : QAlgorithms.Schur.Partition d m × Cells d η → Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ :=
    fun t => E.operator (Sset η t) with hF
  have hFpsd : ∀ t, (F t).PosSemidef := fun t => E.positive _ (Sset_measurable η t)
  have hFsum : ∑ t, F t = 1 := by
    rw [hF, ← povm_finset E Finset.univ (Sset η) (Sset_measurable η) (fun i j h => Sset_disjoint η h),
      iUnion_Sset hη, E.total]
  set R := rep (d := d) hd hm (η := η) with hR
  set Pr : QAlgorithms.Schur.Partition d m × Cells d η → Set ℝ →
      Matrix (Fin n → Bool × Fin d) (Fin n → Bool × Fin d) ℂ := fun t B => specProj (hG (R t)) (g ⁻¹' B) with hPr
  set L : QAlgorithms.Schur.Partition d m × Cells d η →
      Matrix (Fin n → Bool × Fin d) (Fin n → Bool × Fin d) ℂ →ₗ[ℂ]
        Matrix (Register d (m+n) × Register d (m+n)) (Register d (m+n) × Register d (m+n)) ℂ :=
    fun t =>
    { toFun := fun P => (Emb1 (F t) ⊗ₖ Emb2 P).submatrix (eqvR m n) (eqvR m n)
      map_add' := by
        intro P Q
        have : Emb2 (d := d) (P + Q) = Emb2 P + Emb2 Q := by
          unfold Emb2
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          have hb : Pbb b (P + Q) = Pbb b P + Pbb b Q := by ext; simp [Pbb]
          rw [hb, Emb_add, smul_add]
        rw [this, Matrix.kronecker_add]; rfl
      map_smul' := by
        intro c P
        have : Emb2 (d := d) (c • P) = c • Emb2 P := by
          unfold Emb2
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          have hb : Pbb b (c • P) = c • Pbb b P := by ext; simp [Pbb]
          rw [hb, Emb_smul, smul_comm]
        rw [this, Matrix.kronecker_smul]; rfl } with hL
  let op : Set ℝ → Matrix (Register d (m+n) × Register d (m+n)) (Register d (m+n) × Register d (m+n)) ℂ :=
    fun B => ∑ t, L t (Pr t B)
  let M : TwoStateMeasurement d (m + n) :=
    { operator := op
      empty := by
        simp only [op, hPr, Set.preimage_empty, specProj_empty]
        refine Finset.sum_eq_zero (fun t _ => ?_)
        rw [map_zero]
      total := by
        simp only [op, hPr, Set.preimage_univ, specProj_univ, hL, LinearMap.coe_mk, AddHom.coe_mk, Emb2_one]
        have hsub : (∑ t, (Emb1 (F t) ⊗ₖ (1 : Matrix (Fin n → D2 d) (Fin n → D2 d) ℂ)).submatrix (eqvR m n) (eqvR m n)) =
            ((∑ t, Emb1 (F t)) ⊗ₖ (1 : Matrix (Fin n → D2 d) (Fin n → D2 d) ℂ)).submatrix (eqvR m n) (eqvR m n) := by
          ext a b; simp [Matrix.sum_apply, Finset.sum_mul]
        rw [hsub, ← Emb1_sum, hFsum, Emb1_one, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]
      positive := by
        intro B _
        refine Finset.sum_induction _ (fun M : Matrix _ _ ℂ => M.PosSemidef) (fun a b ha hb => ha.add hb)
          PosSemidef.zero (fun t _ => ?_)
        exact ((Emb1_psd (hFpsd t)).kronecker (Emb2_psd (specProj_psd _ _))).submatrix _
      additive := by
        intro B hBm hd'
        have hpre : g ⁻¹' (⋃ i, B i) = ⋃ i, g ⁻¹' (B i) := Set.preimage_iUnion
        refine hasSum_sum (fun t _ => ?_)
        have h1 := specProj_hasSum (hG (R t)) (fun i => g ⁻¹' (B i))
          (fun i j hij => (hd' hij).preimage g)
        rw [← hpre] at h1
        exact h1.map (L t) (LinearMap.continuous_of_finiteDimensional (L t)) }
  refine ⟨M, fun ρ σ hρ hσ hP B hB => ?_⟩
  have hlaw : roundedTomographyLaw m (plus ρ σ) hP =
      ∑ t, ENNReal.ofReal (QAlgorithms.effectProb (F t) (QAlgorithms.piKron m (plus ρ σ))) •
        Measure.dirac (R t) := by
    rw [roundedTomographyLaw, dif_pos ⟨hd, hm⟩, map_eq hd hm hη]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [← (hE (plus ρ σ) hP).1, QAlgorithms.Measurements.bornLaw_apply _ _ _ _ (Sset_measurable η t)]
  have hRpsd := powerState_psd (labelled_psd hρ hσ) n
  rw [hlaw, lintegral_fin_dirac]
  simp only [fun t => spectralLaw_eval (hG (R t)) hRpsd (hg hB)]
  unfold outcomeLaw
  rw [QAlgorithms.Measurements.bornLaw_apply _ _ _ _ hB]
  have hmixH : (QAlgorithms.piKron m (plus ρ σ)).IsHermitian :=
    (QAlgorithms.Tomography.tensorDensity (plus ρ σ) hP m).1.1
  have hEP : QAlgorithms.effectProb (op B) (jointInput (m+n) ρ σ) =
      ∑ t, QAlgorithms.effectProb (F t) (QAlgorithms.piKron m (plus ρ σ)) *
        QAlgorithms.effectProb (Pr t B) (powerState (labelledState ρ σ) n) := by
    unfold QAlgorithms.effectProb
    simp only [op, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp only [hL, LinearMap.coe_mk, AddHom.coe_mk]
    rw [jointInput_eq, trace_sub_equiv, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,
      Emb1_trace _ hρ.2 hσ.2, Emb2_trace _ hρ.2 hσ.2,
      trace_eq_ofReal (hFpsd t).1 hmixH, trace_eq_ofReal (specProj_psd _ _).1 hRpsd.1]
    simp only [Complex.ofReal_re]
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  have hnn1 : ∀ t, 0 ≤ QAlgorithms.effectProb (F t) (QAlgorithms.piKron m (plus ρ σ)) :=
    fun t => QAlgorithms.Measurements.born_nonnegative (hFpsd t) (QAlgorithms.Tomography.tensorDensity _ hP m).1
  have hnn2 : ∀ t, 0 ≤ QAlgorithms.effectProb (Pr t B) (powerState (labelledState ρ σ) n) :=
    fun t => QAlgorithms.Measurements.born_nonnegative (specProj_psd _ _) hRpsd
  rw [hEP, ENNReal.ofReal_sum_of_nonneg (fun t _ => mul_nonneg (hnn1 t) (hnn2 t))]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [ENNReal.ofReal_mul (hnn1 t)]

lemma plus_density {d : ℕ} {ρ σ : Mat d} (hρ : Density ρ) (hσ : Density σ) : Density (plus ρ σ) := by
  refine ⟨(hρ.1.add hσ.1).smul ?_, ?_⟩
  · rw [show (2:ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; rfl]
    exact_mod_cast (by norm_num : (0:ℝ) ≤ 2⁻¹)
  · unfold plus; rw [trace_smul, trace_add, hρ.2, hσ.2]; norm_num


end OTDReal

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
open OptimalTraceDistance.Estimation in
theorem solution : ∀ C : ℝ, 0 < C → ∀ d₀ : ℕ, 2 ≤ d₀ →
    ∀ d : ℕ, 2 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1/32 →
      ∃ M : TwoStateMeasurement d (algorithmCost C d₀ d ε),
        ∀ (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ),
          ∀ B : Set ℝ, MeasurableSet B → outcomeLaw M ρ σ hρ hσ B =
            roundedAlgorithmWeight C d₀ ε ρ σ hρ hσ B := by
  intro C hC d₀ hd₀ d hd ε hε hε1
  have hd0 : 0 < d := by omega
  by_cases hlt : d < d₀
  · have hcost : algorithmCost C d₀ d ε = boundedCount d ε := by rw [algorithmCost, if_pos hlt]
    rw [hcost]
    have hm : 0 < boundedCount d ε := by
      unfold boundedCount constructionC₀
      exact Nat.ceil_pos.2 (by positivity)
    obtain ⟨M, hM⟩ := OTDReal.bounded_real (d := d) (boundedCount d ε) hd0 hm
    refine ⟨M, fun ρ σ hρ hσ B hB => ?_⟩
    rw [hM ρ σ hρ hσ B hB, roundedAlgorithmWeight, if_pos hlt]
  · have hcost : algorithmCost C d₀ d ε = tomographyCount d + freshCount C d ε := by
      rw [algorithmCost, if_neg hlt]
    rw [hcost]
    have hm : 0 < tomographyCount d := by
      unfold tomographyCount constructionC₀
      have hL : 0 < Real.log d := Real.log_pos (by exact_mod_cast (by omega : 1 < d))
      exact Nat.ceil_pos.2 (by positivity)
    have hclip : Measurable clip := by
      have : Continuous clip := by unfold clip; fun_prop
      exact this.measurable
    obtain ⟨M, hM⟩ := OTDReal.main_real (d := d) (tomographyCount d) (freshCount C d ε) hd0 hm
      (fun report => observable (f d ε (reportProjector d report)) (freshCount C d ε))
      (fun r => OTDReal.obs_herm _ _) clip hclip
    refine ⟨M, fun ρ σ hρ hσ B hB => ?_⟩
    have hP := OTDReal.plus_density hρ hσ
    rw [hM ρ σ hρ hσ hP B hB, roundedAlgorithmWeight, if_neg hlt]
    simp only
    rw [dif_pos hP]
