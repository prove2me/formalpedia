-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P38.lemma3_robustDecoupling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T12:05:06.550545+00:00
-- url     : https://prove2.me/submissions/4185ecb0-ab8e-4f6b-83a9-da36b3eca2bc

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P38

noncomputable section

open MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7C18RD

noncomputable instance cen {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) := SeminormedAddGroup.toContinuousENorm

abbrev G (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ

instance haar (d : ℕ) : (QAlgorithms.Schur.unitaryHaar d).IsHaarMeasure := by
  unfold QAlgorithms.Schur.unitaryHaar; infer_instance

instance prob (d : ℕ) : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

lemma int_conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {m n : Type*} [Fintype m]
    [Fintype n] (A : Matrix n m ℂ) (B : Matrix m n ℂ) (f : X → Matrix m m ℂ) (hf : Integrable f μ) :
    ∫ x, A * f x * B ∂μ = A * (∫ x, f x ∂μ) * B := by
  let L0 : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ :=
    { toFun := fun X => A * X * B
      map_add' := fun X Y => by
        show A * (X + Y) * B = A * X * B + A * Y * B
        rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by
        show A * (c • X) * B = c • (A * X * B)
        rw [Matrix.mul_smul, Matrix.smul_mul] }
  let L : Matrix m m ℂ →L[ℂ] Matrix n n ℂ := LinearMap.toContinuousLinearMap L0
  exact L.integral_comp_comm hf

lemma entry {X : Type*} [MeasurableSpace X] {μ : Measure X} {m n : Type*} [Fintype m] [Fintype n]
    (f : X → Matrix m n ℂ) (hf : Integrable f μ) (i : m) (j : n) :
    (∫ x, f x ∂μ) i j = ∫ x, f x i j ∂μ := by
  let L : Matrix m n ℂ →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) j).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : m => (n → ℂ)) i)
  have := L.integral_comp_comm hf
  exact this.symm

lemma int_trace {X : Type*} [MeasurableSpace X] {μ : Measure X} {m : Type*} [Fintype m]
    (f : X → Matrix m m ℂ) (hf : Integrable f μ) :
    ∫ x, (f x).trace ∂μ = (∫ x, f x ∂μ).trace := by
  let L : Matrix m m ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap m ℂ ℂ)
  exact L.integral_comp_comm hf

def M1 {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∫ V : G d, V.val * X * V.valᴴ ∂(QAlgorithms.Schur.unitaryHaar d)

lemma M1_cont {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) : Continuous fun V : G d => V.val * X * V.valᴴ := by
  have hU : Continuous (fun U : G d => (U : Matrix (Fin d) (Fin d) ℂ)) := continuous_subtype_val
  exact (hU.matrix_mul continuous_const).matrix_mul hU.matrix_conjTranspose

lemma M1_int {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) :
    Integrable (fun V : G d => V.val * X * V.valᴴ) (QAlgorithms.Schur.unitaryHaar d) :=
  (M1_cont X).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma unit_left {d : ℕ} (W : G d) : W.valᴴ * W.val = 1 := by
  have := W.2; rw [Matrix.mem_unitaryGroup_iff'] at this; exact this

lemma unit_right {d : ℕ} (W : G d) : W.val * W.valᴴ = 1 := by
  have := W.2; rw [Matrix.mem_unitaryGroup_iff] at this; exact this

lemma M1_inv {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (W : G d) : W.valᴴ * M1 X * W.val = M1 X := by
  unfold M1
  rw [← int_conj _ _ _ (M1_int X)]
  have h := integral_mul_left_eq_self (μ := QAlgorithms.Schur.unitaryHaar d)
    (fun V : G d => V.val * X * V.valᴴ) W⁻¹
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  simp only
  have : ((W⁻¹ * V : G d) : Matrix (Fin d) (Fin d) ℂ) = W.valᴴ * V.val := by
    rw [Submonoid.coe_mul, Matrix.UnitaryGroup.inv_val]; rfl
  rw [this, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

lemma M1_comm {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (W : G d) : M1 X * W.val = W.val * M1 X := by
  have h := M1_inv X W
  calc M1 X * W.val = W.val * (W.valᴴ * M1 X * W.val) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, unit_right, Matrix.one_mul]
    _ = W.val * M1 X := by rw [h]

def Dg {d : ℕ} (i : Fin d) : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal fun k => if k = i then -1 else 1

lemma Dg_unit {d : ℕ} (i : Fin d) : Dg i ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  unfold Dg
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1; funext k
  by_cases h : k = i <;> simp [h]

def Pm {d : ℕ} (σ : Equiv.Perm (Fin d)) : Matrix (Fin d) (Fin d) ℂ := fun a b => if a = σ b then 1 else 0

lemma Pm_unit {d : ℕ} (σ : Equiv.Perm (Fin d)) : Pm σ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext a b
  simp only [Pm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  have : ∀ k : Fin d, ((if a = σ k then (1:ℂ) else 0) * star (if b = σ k then (1:ℂ) else 0)) =
      if k = σ.symm a then (if a = b then 1 else 0) else 0 := by
    intro k
    by_cases h1 : k = σ.symm a
    · subst h1; by_cases hab : a = b <;> simp [hab, Ne.symm]
    · have : a ≠ σ k := by intro h; apply h1; rw [h]; simp
      simp [this, h1]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma M1_offdiag {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) (hij : i ≠ j) : M1 X i j = 0 := by
  have h := congrFun (congrFun (M1_comm X ⟨Dg i, Dg_unit i⟩) i) j
  simp only [Dg, Matrix.mul_diagonal, Matrix.diagonal_mul, Ne.symm hij, if_false, if_true, mul_one] at h
  linear_combination h / 2

lemma M1_diag {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) : M1 X i i = M1 X j j := by
  have h := congrFun (congrFun (M1_comm X ⟨Pm (Equiv.swap i j), Pm_unit _⟩) i) j
  simp only [Matrix.mul_apply, Pm] at h
  simp [Equiv.swap_apply_def] at h
  rw [Finset.sum_eq_single j] at h
  · by_cases hij : i = j
    · subst hij; rfl
    · simpa [hij, Ne.symm hij] using h
  · intro k _ hk
    by_cases h1 : k = i
    · subst h1; simp; intro h'; exact absurd h' hk
    · by_cases h2 : k = j
      · exact absurd h2 hk
      · simp [h1, h2, Ne.symm h1]
  · simp

lemma M1_trace {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) : (M1 X).trace = X.trace := by
  unfold M1
  rw [← int_trace _ (M1_int X)]
  have : ∀ V : G d, (V.val * X * V.valᴴ).trace = X.trace := fun V => by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, unit_left, Matrix.one_mul]
  simp only [this, integral_const, probReal_univ, one_smul]

lemma M1_formula {d : ℕ} (hd : 0 < d) (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    M1 X i j = if i = j then X.trace / d else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, ← M1_trace X, Matrix.trace]
    simp only [Matrix.diag]
    rw [Finset.sum_congr rfl fun k _ => M1_diag X k i]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
  · rw [if_neg hij, M1_offdiag X i j hij]

lemma M1_eq {d : ℕ} (hd : 0 < d) (X : Matrix (Fin d) (Fin d) ℂ) :
    M1 X = (X.trace / d) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext i j
  rw [M1_formula hd, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp

/-- block of psi indexed by environment entries -/
def blk {c e : ℕ} (psi : Matrix (Fin c × Fin e) (Fin c × Fin e) ℂ) (x y : Fin e) :
    Matrix (Fin c) (Fin c) ℂ := fun k l => psi (k, x) (l, y)

lemma kron_entry {I : Type*} [Fintype I] {c e : ℕ} (M : Matrix I (Fin c) ℂ)
    (psi : Matrix (Fin c × Fin e) (Fin c × Fin e) ℂ) (i j : I) (x y : Fin e) :
    (Matrix.kronecker M (1 : Matrix (Fin e) (Fin e) ℂ) * psi *
      (Matrix.kronecker M (1 : Matrix (Fin e) (Fin e) ℂ))ᴴ) (i, x) (j, y) =
      (M * blk psi x y * Mᴴ) i j := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply, blk, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, star_mul', star_one, star_zero]
  have hs : ∀ (p : Prop) [Decidable p] (z : ℂ), star (if p then z else 0) = if p then star z else 0 := by
    intros; split_ifs <;> simp
  simp only [hs, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_ite_eq']
  done

lemma dm_entry {c s b e : ℕ} (W : Matrix (Fin s × Fin b) (Fin c) ℂ)
    (psi : Matrix (Fin c × Fin e) (Fin c × Fin e) ℂ) (U : G c) (x y : Fin b × Fin e) :
    QAlgorithms.Papers.Independent.Gap48.P38.decouplingMarginal W psi U x y =
      ∑ a : Fin s, (W * (U.val * blk psi x.2 y.2 * U.valᴴ) * Wᴴ) (a, x.1) (a, y.1) := by
  simp only [QAlgorithms.Papers.Independent.Gap48.P38.decouplingMarginal]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [kron_entry]
  congr 1
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

lemma card_eq {c s b : ℕ} (W : Matrix (Fin s × Fin b) (Fin c) ℂ) (hW : Wᴴ * W = 1 ∧ W * Wᴴ = 1) :
    (c : ℂ) = (s : ℂ) * b := by
  have h1 := congrArg Matrix.trace hW.1
  have h2 := congrArg Matrix.trace hW.2
  rw [Matrix.trace_mul_comm, h2] at h1
  simp only [Matrix.trace_one, Fintype.card_prod, Fintype.card_fin] at h1
  exact_mod_cast h1.symm

end X7C18RD

open X7C18RD in
theorem X7C18RD_avg (c s b e : ℕ) (hc : 0 < c) (hs : 0 < s) (hb : 0 < b)
    (psi : Matrix (Fin c × Fin e) (Fin c × Fin e) ℂ)
    (W : Matrix (Fin s × Fin b) (Fin c) ℂ)
    (hW : Wᴴ * W = 1 ∧ W * Wᴴ = 1) :
    (∫ U : Matrix.unitaryGroup (Fin c) ℂ,
      QAlgorithms.Papers.Independent.Gap48.P38.decouplingMarginal W psi U ∂QAlgorithms.Schur.unitaryHaar c) =
      Matrix.kronecker (QAlgorithms.Papers.Independent.Information100.P08.maximallyMixed b)
        (QAlgorithms.traceLeft psi) := by
  have hfun : (fun U : G c => QAlgorithms.Papers.Independent.Gap48.P38.decouplingMarginal W psi U) =
      fun U => Matrix.of fun x y =>
        ∑ a : Fin s, (W * (U.val * blk psi x.2 y.2 * U.valᴴ) * Wᴴ) (a, x.1) (a, y.1) := by
    funext U; ext x y; rw [dm_entry]; rfl
  have hcont : ∀ x y : Fin e, Continuous fun U : G c => W * (U.val * blk psi x y * U.valᴴ) * Wᴴ :=
    fun x y => (continuous_const.matrix_mul (M1_cont _)).matrix_mul continuous_const
  have hint : ∀ x y : Fin e, Integrable (fun U : G c => U.val * blk psi x y * U.valᴴ)
      (QAlgorithms.Schur.unitaryHaar c) := fun x y => M1_int _
  have hint2 : ∀ x y : Fin e, Integrable (fun U : G c => W * (U.val * blk psi x y * U.valᴴ) * Wᴴ)
      (QAlgorithms.Schur.unitaryHaar c) := fun x y =>
    (hcont x y).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hF : Continuous fun U : G c => (Matrix.of fun x y =>
        ∑ a : Fin s, (W * (U.val * blk psi x.2 y.2 * U.valᴴ) * Wᴴ) (a, x.1) (a, y.1) :
        Matrix (Fin b × Fin e) (Fin b × Fin e) ℂ) := by
    refine continuous_pi fun x => continuous_pi fun y => ?_
    simp only [Matrix.of_apply]
    exact continuous_finset_sum _ fun a _ => (hcont x.2 y.2).matrix_elem _ _
  rw [hfun]
  ext x y
  rw [entry _ (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  simp only [Matrix.of_apply]
  rw [integral_finset_sum _ (fun a _ => ?_)]
  swap
  · exact ((hcont x.2 y.2).matrix_elem _ _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have : ∀ a : Fin s, ∫ U : G c, (W * (U.val * blk psi x.2 y.2 * U.valᴴ) * Wᴴ) (a, x.1) (a, y.1)
      ∂QAlgorithms.Schur.unitaryHaar c =
      ((blk psi x.2 y.2).trace / c) * (if x.1 = y.1 then 1 else 0) := by
    intro a
    rw [← entry _ (hint2 _ _), int_conj _ _ _ (hint _ _)]
    change (W * M1 (blk psi x.2 y.2) * Wᴴ) _ _ = _
    rw [M1_eq hc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hW.2, Matrix.smul_apply,
      Matrix.one_apply]
    by_cases h : x.1 = y.1
    · simp [h]
    · have : (a, x.1) ≠ (a, y.1) := fun h' => h (Prod.ext_iff.mp h').2
      simp [h, this]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply,
    QAlgorithms.Papers.Independent.Information100.P08.maximallyMixed, Matrix.smul_apply,
    Matrix.one_apply, QAlgorithms.traceLeft, Matrix.of_apply, smul_eq_mul]
  have htr : (blk psi x2 y2).trace = ∑ a, psi (a, x2) (a, y2) := by
    simp [Matrix.trace, blk]
  rw [htr, card_eq W hW]
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  split_ifs <;> field_simp

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P38 in
theorem solution
    (c s b e : ℕ) (hc : 0 < c) (hs : 0 < s) (hb : 0 < b) (he : 0 < e)
    (psi phi : Matrix (Fin c × Fin e) (Fin c × Fin e) ℂ)
    (hpsi : IsDensityMatrix psi) (hphi : IsDensityMatrix phi)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hclose : traceNorm (psi - phi) ≤ epsilon)
    (W : Matrix (Fin s × Fin b) (Fin c) ℂ)
    (hW : Wᴴ * W = 1 ∧ W * Wᴴ = 1) :
    traceNorm ((∫ U : Matrix.unitaryGroup (Fin c) ℂ,
      decouplingMarginal W psi U ∂Schur.unitaryHaar c) -
      Matrix.kronecker (QAlgorithms.Papers.Independent.Information100.P08.maximallyMixed b) (traceLeft psi)) ≤
      2 * epsilon + Real.sqrt ((c : ℝ) * (Matrix.rank (traceLeft phi) : ℝ) *
        frobNorm phi ^ 2 / (s : ℝ) ^ 2) := by
  rw [X7C18RD_avg c s b e hc hs hb psi W hW, sub_self]
  have h0 : traceNorm (0 : Matrix (Fin b × Fin e) (Fin b × Fin e) ℂ) = 0 := by
    simp [traceNorm]
  rw [h0]
  have := Real.sqrt_nonneg ((c : ℝ) * (Matrix.rank (traceLeft phi) : ℝ) * frobNorm phi ^ 2 / (s : ℝ) ^ 2)
  linarith
