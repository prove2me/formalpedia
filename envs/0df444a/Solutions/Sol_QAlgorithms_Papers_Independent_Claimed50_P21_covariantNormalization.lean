-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P21.covariantNormalization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T07:41:58.736606+00:00
-- url     : https://prove2.me/submissions/d3790946-0475-44bd-a298-e2f57f892ece

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P21

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7P21
open QAlgorithms.Papers.Independent.Claimed50.P21

instance suCompact (d : ℕ) : CompactSpace (SU d) := by
  suffices h : IsCompact (Matrix.specialUnitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) from
    isCompact_iff_compactSpace.mp h
  have h1 : IsCompact (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) :=
    isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (Matrix.unitaryGroup (Fin d) ℂ)))
  have h2 : IsClosed {A : Matrix (Fin d) (Fin d) ℂ | A.det = 1} :=
    isClosed_eq (Continuous.matrix_det continuous_id) continuous_const
  have : (Matrix.specialUnitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) =
      (Matrix.unitaryGroup (Fin d) ℂ : Set _) ∩ {A | A.det = 1} := by
    ext A; simp [Matrix.mem_specialUnitaryGroup_iff]
  rw [this]; exact h1.inter_right h2

lemma int_conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {m : Type*} [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) (f : X → Matrix m m ℂ) (hf : Integrable f μ) :
    ∫ x, A * f x * B ∂μ = A * (∫ x, f x ∂μ) * B := by
  let L0 : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ :=
    { toFun := fun X => A * X * B
      map_add' := fun X Y => by simp [mul_add, add_mul]
      map_smul' := fun c X => by simp [Matrix.mul_smul, Matrix.smul_mul] }
  let L : Matrix m m ℂ →L[ℂ] Matrix m m ℂ := LinearMap.toContinuousLinearMap L0
  exact L.integral_comp_comm hf

lemma entry {X : Type*} [MeasurableSpace X] {μ : Measure X} {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (f : X → Matrix m n ℂ) (hf : Integrable f μ) (i : m) (j : n) :
    (∫ x, f x ∂μ) i j = ∫ x, f x i j ∂μ := by
  let L : Matrix m n ℂ →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) j).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : m => (n → ℂ)) i)
  have := L.integral_comp_comm hf
  exact this.symm

lemma int_trace {X : Type*} [MeasurableSpace X] {μ : Measure X} {m : Type*} [Fintype m] [DecidableEq m]
    (f : X → Matrix m m ℂ) (hf : Integrable f μ) :
    ∫ x, (f x).trace ∂μ = (∫ x, f x ∂μ).trace := by
  let L : Matrix m m ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap m ℂ ℂ)
  exact L.integral_comp_comm hf

variable {d : ℕ}

lemma val_cont : Continuous (fun V : SU d => unitaryMatrix V) := continuous_subtype_val

lemma integrable_of_cont {E : Type*} [NormedAddCommGroup E] (H : HaarLaw d) {f : SU d → E}
    (hf : Continuous f) : Integrable f H.law := by
  haveI := H.probability
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma unit_left (W : SU d) : (unitaryMatrix W)ᴴ * unitaryMatrix W = 1 := by
  have := (Matrix.mem_specialUnitaryGroup_iff.mp W.2).1
  rw [Matrix.mem_unitaryGroup_iff'] at this; exact this

lemma unit_right (W : SU d) : unitaryMatrix W * (unitaryMatrix W)ᴴ = 1 := by
  have := (Matrix.mem_specialUnitaryGroup_iff.mp W.2).1
  rw [Matrix.mem_unitaryGroup_iff] at this; exact this

def sinv (W : SU d) : SU d := ⟨(unitaryMatrix W)ᴴ, by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact unit_left W
  · rw [Matrix.det_conjTranspose]
    have := (Matrix.mem_specialUnitaryGroup_iff.mp W.2).2
    simp only [unitaryMatrix] at *; rw [this, star_one]⟩

lemma int_left (H : HaarLaw d) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SU d → E) (hf : Continuous f) (W : SU d) :
    ∫ V, f (W * V) ∂H.law = ∫ V, f V ∂H.law := by
  have hm : Measurable (fun U : SU d => W * U) := (continuous_const.mul continuous_id).measurable
  conv_rhs => rw [← H.left_invariant W]
  rw [integral_map hm.aemeasurable hf.aestronglyMeasurable]

def M1 (H : HaarLaw d) (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∫ V, unitaryMatrix V * X * (unitaryMatrix V)ᴴ ∂H.law

lemma M1_cont (X : Matrix (Fin d) (Fin d) ℂ) :
    Continuous fun V : SU d => unitaryMatrix V * X * (unitaryMatrix V)ᴴ :=
  (val_cont.matrix_mul continuous_const).matrix_mul val_cont.matrix_conjTranspose

lemma M1_inv (H : HaarLaw d) (X : Matrix (Fin d) (Fin d) ℂ) (W : SU d) :
    (unitaryMatrix W)ᴴ * M1 H X * unitaryMatrix W = M1 H X := by
  unfold M1
  rw [← int_conj _ _ _ (integrable_of_cont H (M1_cont X))]
  rw [← int_left H _ (M1_cont X) (sinv W)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  simp only
  have : unitaryMatrix (sinv W * V) = (unitaryMatrix W)ᴴ * unitaryMatrix V := rfl
  rw [this, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

lemma M1_comm (H : HaarLaw d) (X : Matrix (Fin d) (Fin d) ℂ) (W : SU d) :
    M1 H X * unitaryMatrix W = unitaryMatrix W * M1 H X := by
  have h := M1_inv H X W
  calc M1 H X * unitaryMatrix W = unitaryMatrix W * ((unitaryMatrix W)ᴴ * M1 H X * unitaryMatrix W) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, unit_right, Matrix.one_mul]
    _ = unitaryMatrix W * M1 H X := by rw [h]

/-- diagonal special unitary with phases i, -i at positions i, j. -/
def Dg (i j : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun k => if k = i then Complex.I else if k = j then -Complex.I else 1

lemma Dg_mem (i j : Fin d) (hij : i ≠ j) : Dg i j ∈ Matrix.specialUnitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  refine ⟨?_, ?_⟩
  · unfold Dg
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext k
    by_cases h : k = i
    · simp [h]
    · by_cases h' : k = j
      · subst h'; simp [h]
      · simp [h, h']
  · unfold Dg
    rw [Matrix.det_diagonal]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
    rw [Finset.prod_eq_one]
    · simp [Ne.symm hij]
    · intro k hk
      simp only [Finset.mem_erase] at hk
      simp [hk.1, hk.2.1]

/-- signed transposition. -/
def Sw (i j : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  (Equiv.swap i j).permMatrix ℂ * Matrix.diagonal fun k => if k = i then -1 else 1

lemma Sw_mem (i j : Fin d) (hij : i ≠ j) : Sw i j ∈ Matrix.specialUnitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  refine ⟨?_, ?_⟩
  · have hP : (Equiv.swap i j).permMatrix ℂ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
        ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]
    have hD : (Matrix.diagonal fun k : Fin d => if k = i then (-1 : ℂ) else 1) ∈
        Matrix.unitaryGroup (Fin d) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext k; by_cases h : k = i <;> simp [h]
    have := Submonoid.mul_mem _ hP hD
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at this
    exact this
  · rw [Sw, Matrix.det_mul, Matrix.det_permutation, Matrix.det_diagonal,
      Finset.prod_ite_eq' Finset.univ i]
    simp [Equiv.Perm.sign_swap hij]


lemma M1_offdiag (H : HaarLaw d) (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) (hij : i ≠ j) :
    M1 H X i j = 0 := by
  have h := congrFun (congrFun (M1_comm H X ⟨Dg i j, Dg_mem i j hij⟩) i) j
  simp only [unitaryMatrix, Dg, Matrix.mul_diagonal, Matrix.diagonal_mul, Ne.symm hij, if_false, if_true] at h
  have hI : (2 : ℂ) * Complex.I ≠ 0 := by simp
  have : (2 * Complex.I) * M1 H X i j = 0 := by linear_combination -h
  simpa [hI] using this

lemma M1_diag (H : HaarLaw d) (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    M1 H X i i = M1 H X j j := by
  by_cases hij : i = j
  · rw [hij]
  have h := congrFun (congrFun (M1_comm H X ⟨Sw i j, Sw_mem i j hij⟩) i) j
  simp only [unitaryMatrix, Sw, ← Matrix.mul_assoc, Matrix.mul_diagonal] at h
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Ne.symm hij,
    Equiv.swap_apply_def] at h
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j] at h
  · simpa [hij, Ne.symm hij] using h
  · intro x _ hx; simp [hx, Ne.symm hx]
  · simp
  · intro x _ hx
    by_cases hxj : x = j
    · subst hxj; simp [hij, hx]
    · simp [hx, hxj]
  · simp

lemma M1_trace (H : HaarLaw d) (X : Matrix (Fin d) (Fin d) ℂ) : (M1 H X).trace = X.trace := by
  haveI := H.probability
  unfold M1
  rw [← int_trace _ (integrable_of_cont H (M1_cont X))]
  have : ∀ V : SU d, (unitaryMatrix V * X * (unitaryMatrix V)ᴴ).trace = X.trace := fun V => by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, unit_left, Matrix.one_mul]
  simp only [this, integral_const, probReal_univ, one_smul]

lemma M1_formula (H : HaarLaw d) (hd : 0 < d) (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    M1 H X i j = if i = j then X.trace / d else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, ← M1_trace H X, Matrix.trace]
    simp only [Matrix.diag]
    rw [Finset.sum_congr rfl fun k _ => M1_diag H X k i]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
  · rw [if_neg hij, M1_offdiag H X i j hij]

end X7P21

namespace X7P21

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def ptr (M : Matrix (ι × κ) (ι × κ) ℂ) : Matrix κ κ ℂ := fun k k' => ∑ i, M (i, k) (i, k')

lemma ptr_kron_one_comm (A : Matrix ι ι ℂ) (N : Matrix (ι × κ) (ι × κ) ℂ) :
    ptr ((A ⊗ₖ (1 : Matrix κ κ ℂ)) * N) = ptr (N * (A ⊗ₖ (1 : Matrix κ κ ℂ))) := by
  ext k k'
  simp only [ptr, Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma ptr_one_kron_mul (B : Matrix κ κ ℂ) (N : Matrix (ι × κ) (ι × κ) ℂ) :
    ptr (((1 : Matrix ι ι ℂ) ⊗ₖ B) * N) = B * ptr N := by
  ext k k'
  simp only [ptr, Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type_right, Matrix.one_apply]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.mul_sum]
  rw [Finset.sum_comm]

lemma ptr_mul_one_kron (B : Matrix κ κ ℂ) (N : Matrix (ι × κ) (ι × κ) ℂ) :
    ptr (N * ((1 : Matrix ι ι ℂ) ⊗ₖ B)) = ptr N * B := by
  ext k k'
  simp only [ptr, Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type_right, Matrix.one_apply]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma ptr_conj (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (hA : Aᴴ * A = 1) (M : Matrix (ι × κ) (ι × κ) ℂ) :
    ptr ((A ⊗ₖ B) * M * (A ⊗ₖ B)ᴴ) = B * ptr M * Bᴴ := by
  have h1 : A ⊗ₖ B = (A ⊗ₖ (1 : Matrix κ κ ℂ)) * ((1 : Matrix ι ι ℂ) ⊗ₖ B) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have h2 : (A ⊗ₖ B)ᴴ = ((1 : Matrix ι ι ℂ) ⊗ₖ Bᴴ) * (Aᴴ ⊗ₖ (1 : Matrix κ κ ℂ)) := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [h2, h1]
  simp only [Matrix.mul_assoc]
  rw [ptr_kron_one_comm]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_kronecker_mul, hA, Matrix.mul_one, Matrix.one_kronecker_one, Matrix.mul_one,
    ptr_one_kron_mul, ← Matrix.mul_assoc, ptr_mul_one_kron, Matrix.mul_assoc]

lemma ptr_trace (M : Matrix (ι × κ) (ι × κ) ℂ) : (ptr M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, ptr, Fintype.sum_prod_type]
  exact Finset.sum_comm

def ptrE (i : ι) : Matrix (ι × κ) κ ℂ := Matrix.of fun p k => if p.1 = i ∧ p.2 = k then 1 else 0

lemma ptr_psd (M : Matrix (ι × κ) (ι × κ) ℂ) (hM : M.PosSemidef) : (ptr M).PosSemidef := by
  have : ptr M = ∑ i : ι, (ptrE (κ := κ) i)ᴴ * M * ptrE (κ := κ) i := by
    ext k k'
    simp only [ptr, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, ptrE, Fintype.sum_prod_type, ite_and, Finset.sum_ite_irrel, apply_ite (starRingEnd ℂ), ite_mul]
  rw [this]
  exact Matrix.posSemidef_sum _ fun i _ => hM.conjTranspose_mul_mul_same _

end X7P21

namespace X7P21
open QAlgorithms.Papers.Independent.Claimed50.P21

lemma kron_cont {X : Type*} [TopologicalSpace X] {l m n p : Type*} {A : X → Matrix l m ℂ}
    {B : X → Matrix n p ℂ} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => A x ⊗ₖ B x :=
  continuous_matrix fun i j => by
    simp only [Matrix.kroneckerMap_apply]
    exact (hA.matrix_elem _ _).mul (hB.matrix_elem _ _)

lemma bar_unit {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ) (h : Uᴴ * U = 1) :
    (U.map conj)ᴴ * U.map conj = 1 := by
  have e : (U.map conj)ᴴ = (Uᴴ).map conj := by ext i j; simp [Matrix.conjTranspose_apply]
  rw [e, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]

lemma kron_unit {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) :
    (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hA, hB, Matrix.one_kronecker_one]

lemma unit_comm {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ) (h : Uᴴ * U = 1) :
    U * Uᴴ = 1 := mul_eq_one_comm.mp h

variable {d : ℕ}

lemma ubar_unit (V : SU d) : ((unitaryMatrix V).map conj)ᴴ * (unitaryMatrix V).map conj = 1 :=
  bar_unit _ (unit_left V)

lemma rep_unit (V W : SU d) : (representation V W)ᴴ * representation V W = 1 := by
  unfold representation
  exact kron_unit _ _ (kron_unit _ _ (unit_left V) (ubar_unit V)) (kron_unit _ _ (unit_left W) (ubar_unit W))

lemma cD_cont (X : Matrix (Four d) (Four d) ℂ) : Continuous (covariantDensity X) := by
  have hr : Continuous fun V : SU d => representation V 1 := by
    unfold representation
    exact kron_cont (kron_cont val_cont (val_cont.matrix_map (Complex.continuous_conj)))
      continuous_const
  unfold covariantDensity covarianceAction
  exact (hr.matrix_mul continuous_const).matrix_mul hr.matrix_conjTranspose

/-- integral of PSD-valued functions is PSD -/
lemma int_psd {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} {n : Type*} [Fintype n] [DecidableEq n]
    (f : Y → Matrix n n ℂ) (hf : Integrable f μ) (hp : ∀ y, (f y).PosSemidef) :
    (∫ y, f y ∂μ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v => ?_⟩
  · ext i j
    rw [Matrix.conjTranspose_apply, entry _ hf, entry _ hf]
    rw [show star (∫ y, f y j i ∂μ) = conj (∫ y, f y j i ∂μ) from rfl, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have := congrFun (congrFun (hp y).isHermitian i) j
    rw [Matrix.conjTranspose_apply] at this
    exact this
  · let L0 : Matrix n n ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun M => star v ⬝ᵥ (M *ᵥ v)
        map_add' := fun M N => by simp [Matrix.add_mulVec, dotProduct_add]
        map_smul' := fun c M => by simp [Matrix.smul_mulVec, dotProduct_smul] }
    let L : Matrix n n ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap L0
    have h1 : star v ⬝ᵥ ((∫ y, f y ∂μ) *ᵥ v) = ∫ y, star v ⬝ᵥ (f y *ᵥ v) ∂μ :=
      (L.integral_comp_comm hf).symm
    have hg : ∀ y, star v ⬝ᵥ (f y *ᵥ v) = (((star v ⬝ᵥ (f y *ᵥ v)).re : ℝ) : ℂ) := by
      intro y
      have := ((Matrix.posSemidef_iff_dotProduct_mulVec.mp (hp y)).2 v)
      rw [Complex.nonneg_iff] at this
      apply Complex.ext <;> simp [← this.2]
    rw [h1, integral_congr_ae (Filter.Eventually.of_forall hg), integral_complex_ofReal]
    apply Complex.zero_le_real.mpr
    apply integral_nonneg
    intro y
    have := ((Matrix.posSemidef_iff_dotProduct_mulVec.mp (hp y)).2 v)
    exact (Complex.nonneg_iff.mp this).1


abbrev ub (V : SU d) : Matrix (Wire d) (Wire d) ℂ := (unitaryMatrix V).map conj

lemma M1c (H : HaarLaw d) (hd : 0 < d) (Y : Matrix (Wire d) (Wire d) ℂ) (b b' : Wire d) :
    ∫ V, (ub V * Y * (ub V)ᴴ) b b' ∂H.law = if b = b' then Y.trace / d else 0 := by
  have e : ∀ V : SU d, (ub V * Y * (ub V)ᴴ) b b' =
      conj ((unitaryMatrix V * Y.map conj * (unitaryMatrix V)ᴴ) b b') := by
    intro V
    have : ub V * Y * (ub V)ᴴ = (unitaryMatrix V * Y.map conj * (unitaryMatrix V)ᴴ).map conj := by
      rw [Matrix.map_mul, Matrix.map_mul]
      congr 1
      · congr 1; ext i j; simp
      all_goals try (ext i j; simp [Matrix.conjTranspose_apply])
    rw [this, Matrix.map_apply]
  simp_rw [e]
  rw [integral_conj, ← entry _ (integrable_of_cont H (M1_cont _))]
  have := M1_formula H hd (Y.map conj) b b'
  unfold M1 at this
  rw [this]
  have ht : (Y.map conj).trace = conj Y.trace := by simp [Matrix.trace, map_sum]
  split_ifs <;> simp [ht]

def slice {κ : Type*} (Y : Matrix (Wire d × κ) (Wire d × κ) ℂ) (k k' : κ) : Matrix (Wire d) (Wire d) ℂ :=
  Matrix.of fun β β' => Y (β, k) (β', k')

lemma slice_entry {κ : Type*} [Fintype κ] [DecidableEq κ] (B : Matrix (Wire d) (Wire d) ℂ)
    (Y : Matrix (Wire d × κ) (Wire d × κ) ℂ) (b b' : Wire d) (k k' : κ) :
    ((B ⊗ₖ (1 : Matrix κ κ ℂ)) * Y * (B ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ) (b, k) (b', k') =
      (B * slice Y k k' * Bᴴ) b b' := by
  simp only [slice, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, Matrix.of_apply]
  simp only [Complex.star_def, apply_ite (starRingEnd ℂ), map_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul]


abbrev TT (d : ℕ) := Equiv.prodAssoc (Wire d) (Wire d) (Wire d × Wire d)

lemma one_bar : ((1 : Matrix (Wire d) (Wire d) ℂ).map conj) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

lemma rep1 (V : SU d) : representation V 1 =
    (unitaryMatrix V ⊗ₖ ub V) ⊗ₖ (1 : Matrix (Wire d × Wire d) (Wire d × Wire d) ℂ) := by
  unfold representation
  have : unitaryMatrix (1 : SU d) = 1 := rfl
  rw [this, one_bar, Matrix.one_kronecker_one]

lemma cD_ptr (X : Matrix (Four d) (Four d) ℂ) (V : SU d) (b b' : Wire d) (k k' : Wire d × Wire d) :
    ∑ a, covariantDensity X V ((a, b), k) ((a, b'), k') =
      (ub V * slice (ptr (X.submatrix (TT d).symm (TT d).symm)) k k' * (ub V)ᴴ) b b' := by
  have h : ∑ a, covariantDensity X V ((a, b), k) ((a, b'), k') =
      ptr ((covariantDensity X V).submatrix (TT d).symm (TT d).symm) (b, k) (b', k') := rfl
  rw [h, covariantDensity, covarianceAction, rep1]
  rw [← Matrix.submatrix_mul_equiv _ _ _ (TT d).symm _, ← Matrix.submatrix_mul_equiv _ _ _ (TT d).symm _,
    ← Matrix.conjTranspose_submatrix, Matrix.kronecker_assoc', ptr_conj _ _ (unit_left V)]
  exact slice_entry _ _ _ _ _ _


lemma slice_trace (X : Matrix (Four d) (Four d) ℂ) (k k' : Wire d × Wire d) :
    (slice (ptr (X.submatrix (TT d).symm (TT d).symm)) k k').trace = ptr X k k' := by
  simp only [slice, ptr, Matrix.trace, Matrix.diag, Matrix.of_apply, Matrix.submatrix_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  rfl

lemma Z_inv (X : Matrix (Four d) (Four d) ℂ) (hc : SeedCommutes X) (V : SU d) :
    ub V * ptr (ptr X) * (ub V)ᴴ = ptr (ptr X) := by
  have hR := rep_unit V V
  have hX : X = representation V V * X * (representation V V)ᴴ := by
    rw [← hc V, Matrix.mul_assoc, unit_comm _ hR, Matrix.mul_one]
  conv_rhs => rw [hX]
  unfold representation
  rw [ptr_conj _ _ (kron_unit _ _ (unit_left V) (ubar_unit V)), ptr_conj _ _ (unit_left V)]

theorem main (d : ℕ) (hd : 2 ≤ d) (H : HaarLaw d)
    (X : Matrix (Four d) (Four d) ℂ) (hX : X.PosSemidef) (hc : SeedCommutes X) :
    IsDeterministicTwoComb (∫ V, covariantDensity X V ∂H.law) ↔ X.trace = (d : ℂ)^2 := by
  haveI := H.probability
  have hd0 : 0 < d := by omega
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hint : Integrable (covariantDensity X) H.law := integrable_of_cont H (cD_cont X)
  have hint2 : ∀ i j, Integrable (fun V => covariantDensity X V i j) H.law :=
    fun i j => integrable_of_cont H ((cD_cont X).matrix_elem i j)
  set I := ∫ V, covariantDensity X V ∂H.law with hI
  have htr : I.trace = X.trace := by
    rw [hI, ← int_trace _ hint]
    have : ∀ V : SU d, (covariantDensity X V).trace = X.trace := fun V => by
      rw [covariantDensity, covarianceAction, Matrix.trace_mul_comm, ← Matrix.mul_assoc, rep_unit,
        Matrix.one_mul]
    simp only [this, integral_const, probReal_univ, one_smul]
  have hsum1 : ∀ (b b' : Wire d) (k k' : Wire d × Wire d),
      ∑ a, I ((a, b), k) ((a, b'), k') = if b = b' then ptr X k k' / d else 0 := by
    intro b b' k k'
    simp only [hI, entry _ hint]
    rw [← integral_finset_sum _ (fun a _ => hint2 _ _)]
    simp_rw [cD_ptr]
    rw [M1c H hd0, slice_trace]
  constructor
  · rintro ⟨_, Rone, _, h1, h2⟩
    rw [← htr]
    have e1 : I.trace = ∑ b, ∑ c, ∑ e, ∑ a, I ((a, b), (c, e)) ((a, b), (c, e)) := by
      simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_comm]
    rw [e1]
    simp only [h1, if_true, one_mul]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_comm]
    simp only [h2, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  · intro ht
    refine ⟨int_psd _ hint (fun V => hX.mul_mul_conjTranspose_same _),
      (((d : ℝ)⁻¹ : ℝ) : ℂ) • ptr X, (ptr_psd X hX).smul (Complex.zero_le_real.mpr (by positivity)), ?_, ?_⟩
    · intro b c e b' c' e'
      rw [hsum1 b b' (c, e) (c', e')]
      split_ifs <;> simp [Matrix.smul_apply] <;> field_simp
    · intro e e'
      have hZ : ptr (ptr X) e e' = if e = e' then (ptr (ptr X)).trace / d else 0 := by
        rw [← M1c H hd0]
        have : ∀ V : SU d, (ub V * ptr (ptr X) * (ub V)ᴴ) e e' = ptr (ptr X) e e' := fun V => by
          rw [Z_inv X hc V]
        simp only [this, integral_const, probReal_univ, one_smul]
      have : ∑ c, ((((d : ℝ)⁻¹ : ℝ) : ℂ) • ptr X) (c, e) (c, e') = (d : ℂ)⁻¹ * ptr (ptr X) e e' := by
        simp [Matrix.smul_apply, ptr, Finset.mul_sum]
      rw [this, hZ, ptr_trace, ptr_trace, ht]
      split_ifs <;> field_simp <;> simp

end X7P21


attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

open QAlgorithms.Papers.Independent.Claimed50.P21 in
theorem solution (d : ℕ) (hd : 2 ≤ d) (H : HaarLaw d)
    (X : Matrix (Four d) (Four d) ℂ) (hX : X.PosSemidef) (hc : SeedCommutes X) :
    IsDeterministicTwoComb (∫ V, covariantDensity X V ∂H.law) ↔ X.trace = (d : ℂ)^2 :=
  X7P21.main d hd H X hX hc

end
