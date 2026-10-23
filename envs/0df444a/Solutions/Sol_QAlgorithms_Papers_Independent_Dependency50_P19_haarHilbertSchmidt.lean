-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P19.haarHilbertSchmidt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:41:59.131346+00:00
-- url     : https://prove2.me/submissions/0ef82d8c-71a7-4dd7-bc02-3f28dd2c0633

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

noncomputable section
namespace X7N2

attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable instance X7N2_cen {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) := SeminormedAddGroup.toContinuousENorm

instance X7N2_haar (d : ℕ) : (QAlgorithms.Schur.unitaryHaar d).IsHaarMeasure := by
  unfold QAlgorithms.Schur.unitaryHaar; infer_instance

abbrev G (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ

def KK {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.kronecker U U

def ff {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (U : G d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (KK (U : Matrix (Fin d) (Fin d) ℂ))ᴴ * S * KK (U : Matrix (Fin d) (Fin d) ℂ)

lemma X7N2_KK_cont (d : ℕ) : Continuous (fun U : G d => KK (U : Matrix (Fin d) (Fin d) ℂ)) := by
  have hU : Continuous (fun U : G d => (U : Matrix (Fin d) (Fin d) ℂ)) := continuous_subtype_val
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [KK]
  exact (hU.matrix_elem i.1 j.1).mul (hU.matrix_elem i.2 j.2)

lemma X7N2_ff_cont {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Continuous (ff S) := by
  unfold ff
  exact ((X7N2_KK_cont d).matrix_conjTranspose.matrix_mul continuous_const).matrix_mul (X7N2_KK_cont d)

lemma X7N2_ff_int {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Integrable (ff S) (QAlgorithms.Schur.unitaryHaar d) :=
  (X7N2_ff_cont S).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma X7N2_KK_mul {d : ℕ} (U V : Matrix (Fin d) (Fin d) ℂ) : KK (U * V) = KK U * KK V := by
  unfold KK; simp only [Matrix.kronecker]; rw [Matrix.mul_kronecker_mul]

lemma X7N2_KK_unit {d : ℕ} (U : G d) : (KK (U : Matrix (Fin d) (Fin d) ℂ))ᴴ * KK (U : Matrix (Fin d) (Fin d) ℂ) = 1 ∧
    KK (U : Matrix (Fin d) (Fin d) ℂ) * (KK (U : Matrix (Fin d) (Fin d) ℂ))ᴴ = 1 := by
  have h1 : (U : Matrix (Fin d) (Fin d) ℂ)ᴴ * U = 1 := Matrix.UnitaryGroup.star_mul_self U
  have h2 : (U : Matrix (Fin d) (Fin d) ℂ) * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp U.2
    rwa [Matrix.star_eq_conjTranspose] at this
  unfold KK
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, h1, h2]
  simp


lemma X7N2_phase_aux {X : Type*} [DecidableEq X] (a b c e : X)
    (h : ∀ s : X, ((if a = s then Complex.I else 1) * (if b = s then Complex.I else 1)) =
      ((if c = s then Complex.I else 1) * (if e = s then Complex.I else 1))) :
    (a = c ∧ b = e) ∨ (a = e ∧ b = c) := by
  have hI1 : Complex.I ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp at this
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hm1 : (-1 : ℂ) ≠ 1 := by norm_num
  have hmI : (-1 : ℂ) ≠ Complex.I := by
    intro h; have := congrArg Complex.im h; simp at this
  have ha := h a
  have hb := h b
  by_cases hac : a = c <;> by_cases hae : a = e <;> by_cases hbc : b = c <;> by_cases hbe : b = e <;>
    by_cases hab : a = b <;> by_cases hce : c = e <;> subst_vars <;>
    simp_all [eq_comm]

lemma X7N2_diag_unit {d : ℕ} (s : Fin d) :
    Matrix.diagonal (fun t : Fin d => if t = s then Complex.I else 1) ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1; funext t
  by_cases h : t = s <;> simp [h]

lemma X7N2_phase {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : ∀ V : G d, M * KK (V : Matrix (Fin d) (Fin d) ℂ) = KK (V : Matrix (Fin d) (Fin d) ℂ) * M)
    (i j k l : Fin d) (hne : M (i, j) (k, l) ≠ 0) : (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  apply X7N2_phase_aux
  intro s
  have := congrFun (congrFun (hM ⟨_, X7N2_diag_unit s⟩) (i, j)) (k, l)
  simp only [KK, Matrix.kronecker, Matrix.diagonal_kronecker_diagonal, Matrix.mul_diagonal,
    Matrix.diagonal_mul] at this
  have := mul_left_cancel₀ hne (this.trans (mul_comm _ _))
  exact this.symm

def Pm {d : ℕ} (σ : Equiv.Perm (Fin d)) : Matrix (Fin d) (Fin d) ℂ := fun a b => if a = σ b then 1 else 0

lemma X7N2_Pm_unit {d : ℕ} (σ : Equiv.Perm (Fin d)) : Pm σ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
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

lemma X7N2_perm {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : ∀ V : G d, M * KK (V : Matrix (Fin d) (Fin d) ℂ) = KK (V : Matrix (Fin d) (Fin d) ℂ) * M)
    (σ : Equiv.Perm (Fin d)) (a b c e : Fin d) : M (σ a, σ b) (σ c, σ e) = M (a, b) (c, e) := by
  have := congrFun (congrFun (hM ⟨_, X7N2_Pm_unit σ⟩) (σ a, σ b)) (c, e)
  simp only [KK, Matrix.kronecker, Matrix.mul_apply, Matrix.kroneckerMap_apply, Pm,
    Fintype.sum_prod_type] at this
  simp [ite_mul, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq] at this
  exact this

def ww {d : ℕ} (i0 i1 : Fin d) : Fin d → ℂ := fun k => if k = i0 then 3/5 else if k = i1 then 4/5 else 0

def Hh {d : ℕ} (i0 i1 : Fin d) : Matrix (Fin d) (Fin d) ℂ := 1 - (2 : ℂ) • Matrix.vecMulVec (ww i0 i1) (ww i0 i1)

lemma X7N2_ww_star {d : ℕ} (i0 i1 : Fin d) : star (ww i0 i1) = ww i0 i1 := by
  funext k; simp only [Pi.star_apply, ww]; split_ifs <;> simp

lemma X7N2_ww_dot {d : ℕ} (i0 i1 : Fin d) (h01 : i0 ≠ i1) : ww i0 i1 ⬝ᵥ ww i0 i1 = 1 := by
  have : ∀ k, ww i0 i1 k * ww i0 i1 k = (if k = i0 then (9/25 : ℂ) else 0) + (if k = i1 then (16/25 : ℂ) else 0) := by
    intro k; simp only [ww]
    by_cases h0 : k = i0
    · subst h0; simp [h01]; norm_num
    · by_cases h1 : k = i1
      · subst h1; simp [h0]; norm_num
      · simp [h0, h1]
  simp only [dotProduct, this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num

lemma X7N2_Hh_unit {d : ℕ} (i0 i1 : Fin d) (h01 : i0 ≠ i1) : Hh i0 i1 ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  have hP : (Matrix.vecMulVec (ww i0 i1) (ww i0 i1))ᴴ = Matrix.vecMulVec (ww i0 i1) (ww i0 i1) := by
    rw [Matrix.conjTranspose_vecMulVec, X7N2_ww_star]
  have hPP : Matrix.vecMulVec (ww i0 i1) (ww i0 i1) * Matrix.vecMulVec (ww i0 i1) (ww i0 i1) =
      Matrix.vecMulVec (ww i0 i1) (ww i0 i1) := by
    rw [Matrix.vecMulVec_mul_vecMulVec, X7N2_ww_dot i0 i1 h01, one_smul]
  unfold Hh
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hP, Matrix.conjTranspose_one]
  simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hPP, smul_smul]
  have h2 : star (2 : ℂ) = 2 := by simp
  rw [h2]
  module

lemma X7N2_house {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : ∀ V : G d, M * KK (V : Matrix (Fin d) (Fin d) ℂ) = KK (V : Matrix (Fin d) (Fin d) ℂ) * M)
    (i0 i1 : Fin d) (h01 : i0 ≠ i1) (z x y : ℂ)
    (hrow : ∀ q, M (i0, i0) q = if q = (i0, i0) then z else 0)
    (hcol : ∀ p, M p (i0, i1) = (if p = (i0, i1) then x else 0) + (if p = (i1, i0) then y else 0)) :
    z = x + y := by
  have := congrFun (congrFun (hM ⟨_, X7N2_Hh_unit i0 i1 h01⟩) (i0, i0)) (i0, i1)
  simp only [Matrix.mul_apply, hrow, hcol, ite_mul, zero_mul, mul_add, mul_ite, mul_zero,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  have h00 : Hh i0 i1 i0 i0 = 7/25 := by
    simp [Hh, ww, Matrix.vecMulVec_apply]; norm_num
  have h01' : Hh i0 i1 i0 i1 = -24/25 := by
    simp [Hh, ww, Matrix.vecMulVec_apply, h01, Ne.symm h01]; norm_num
  simp only [KK, Matrix.kronecker, Matrix.kroneckerMap_apply, h00, h01'] at this
  have hc : ((7:ℂ)/25 * (-24/25)) ≠ 0 := by norm_num
  have h2 : ((-24:ℂ)/25 * (7/25)) = 7/25 * (-24/25) := by ring
  rw [h2] at this
  have := mul_left_cancel₀ hc (by rw [mul_comm] at this; rw [this]; ring : (7/25 * (-24/25) : ℂ) * z = 7/25 * (-24/25) * (x + y))
  exact this

lemma X7N2_pair {d : ℕ} (i0 i1 i j : Fin d) (h01 : i0 ≠ i1) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin d), σ i0 = i ∧ σ i1 = j := by
  refine ⟨(Equiv.swap i0 i).trans (Equiv.swap (Equiv.swap i0 i i1) j), ?_, ?_⟩
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]
    have : i ≠ Equiv.swap i0 i i1 := by
      intro h
      have : Equiv.swap i0 i i0 = Equiv.swap i0 i i1 := by rw [Equiv.swap_apply_left]; exact h
      exact h01 ((Equiv.swap i0 i).injective this)
    rw [Equiv.swap_apply_of_ne_of_ne this hij]
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]

theorem X7N2_comm {d : ℕ} (hd : 2 ≤ d) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : ∀ V : G d, M * KK (V : Matrix (Fin d) (Fin d) ℂ) = KK (V : Matrix (Fin d) (Fin d) ℂ) * M) :
    ∃ x y : ℂ, ∀ i j k l : Fin d,
      M (i, j) (k, l) = (if i = k ∧ j = l then x else 0) + (if i = l ∧ j = k then y else 0) := by
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  set x := M (i0, i1) (i0, i1)
  set y := M (i0, i1) (i1, i0)
  set z := M (i0, i0) (i0, i0)
  have hdiag : ∀ i, M (i, i) (i, i) = z := by
    intro i
    have := X7N2_perm M hM (Equiv.swap i0 i) i0 i0 i0 i0
    simpa using this
  have hx : ∀ i j, i ≠ j → M (i, j) (i, j) = x := by
    intro i j hij
    obtain ⟨σ, h1, h2⟩ := X7N2_pair i0 i1 i j h01 hij
    have := X7N2_perm M hM σ i0 i1 i0 i1
    rwa [h1, h2] at this
  have hy : ∀ i j, i ≠ j → M (i, j) (j, i) = y := by
    intro i j hij
    obtain ⟨σ, h1, h2⟩ := X7N2_pair i0 i1 i j h01 hij
    have := X7N2_perm M hM σ i0 i1 i1 i0
    rwa [h1, h2] at this
  have hrow : ∀ q, M (i0, i0) q = if q = (i0, i0) then z else 0 := by
    rintro ⟨k, l⟩
    by_cases hq : (k, l) = (i0, i0)
    · rw [if_pos hq, hq]
    · rw [if_neg hq]
      by_contra hne
      rcases X7N2_phase M hM i0 i0 k l hne with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;>
        exact hq rfl
  have hcol : ∀ p, M p (i0, i1) = (if p = (i0, i1) then x else 0) + (if p = (i1, i0) then y else 0) := by
    rintro ⟨k, l⟩
    by_cases hq : (k, l) = (i0, i1)
    · have h2 : (k, l) ≠ (i1, i0) := by
        rw [hq]; intro h; simp only [Prod.mk.injEq] at h; exact h01 h.1
      rw [if_pos hq, if_neg h2, hq, add_zero]
    · by_cases hq2 : (k, l) = (i1, i0)
      · rw [if_neg hq, if_pos hq2, hq2, zero_add]
        exact hy i1 i0 (Ne.symm h01)
      · rw [if_neg hq, if_neg hq2, add_zero]
        by_contra hne
        rcases X7N2_phase M hM k l i0 i1 hne with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
        · exact hq rfl
        · exact hq2 rfl
  have hz : z = x + y := X7N2_house M hM i0 i1 h01 z x y hrow hcol
  refine ⟨x, y, fun i j k l => ?_⟩
  by_cases hA : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := hA
    by_cases hij : i = j
    · subst hij; simp [hdiag, hz]
    · rw [hx i j hij]; simp [hij]
  · by_cases hB : i = l ∧ j = k
    · obtain ⟨rfl, rfl⟩ := hB
      have hij : i ≠ j := by intro h; apply hA; exact ⟨h, h.symm⟩
      rw [hy i j hij]; simp [hA]
    · rw [if_neg hA, if_neg hB, add_zero]
      by_contra hne
      rcases X7N2_phase M hM i j k l hne with h | h
      · exact hA h
      · exact hB h

instance X7N2_prob (d : ℕ) : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

lemma X7N2_mapRight (d : ℕ) (g : G d) :
    Measure.map (· * g) (QAlgorithms.Schur.unitaryHaar d) = QAlgorithms.Schur.unitaryHaar d := by
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace
    (Measure.map (· * g) (QAlgorithms.Schur.unitaryHaar d)) (QAlgorithms.Schur.unitaryHaar d)
  have hu : Measure.map (· * g) (QAlgorithms.Schur.unitaryHaar d) Set.univ = 1 := by
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ]
    simp
  set c := Measure.haarScalarFactor (Measure.map (· * g) (QAlgorithms.Schur.unitaryHaar d))
      (QAlgorithms.Schur.unitaryHaar d) with hcdef
  have hc : c = 1 := by
    have := congrArg (fun m : Measure (G d) => m Set.univ) h
    simp only [Measure.smul_apply, measure_univ] at this
    rw [hu, ENNReal.smul_def, smul_eq_mul, mul_one] at this
    exact_mod_cast this.symm
  rw [h, hc, one_smul]

lemma X7N2_intRight (d : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : G d → E) (g : G d) :
    ∫ U, f (U * g) ∂(QAlgorithms.Schur.unitaryHaar d) = ∫ U, f U ∂(QAlgorithms.Schur.unitaryHaar d) := by
  have hm : MeasurableEmbedding (· * g : G d → G d) := (MeasurableEquiv.mulRight g).measurableEmbedding
  rw [← hm.integral_map, X7N2_mapRight]

lemma X7N2_entry' {X : Type*} [MeasurableSpace X] {μ : Measure X} {m n : Type*} [Fintype m] [Fintype n]
    (f : X → Matrix m n ℂ) (hf : Integrable f μ) (i : m) (j : n) :
    (∫ x, f x ∂μ) i j = ∫ x, f x i j ∂μ := by
  let L : Matrix m n ℂ →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) j).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : m => (n → ℂ)) i)
  have := L.integral_comp_comm hf
  exact this.symm


lemma X7N2_int_conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {m : Type*} [Fintype m]
    (A B : Matrix m m ℂ) (f : X → Matrix m m ℂ) (hf : Integrable f μ) :
    ∫ x, A * f x * B ∂μ = A * (∫ x, f x ∂μ) * B := by
  let L0 : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ :=
    { toFun := fun X => A * X * B
      map_add' := fun X Y => by simp [mul_add, add_mul]
      map_smul' := fun c X => by simp [Matrix.mul_smul, Matrix.smul_mul] }
  let L : Matrix m m ℂ →L[ℂ] Matrix m m ℂ := LinearMap.toContinuousLinearMap L0
  exact L.integral_comp_comm hf

lemma X7N2_int_trace {X : Type*} [MeasurableSpace X] {μ : Measure X} {m : Type*} [Fintype m]
    (f : X → Matrix m m ℂ) (hf : Integrable f μ) :
    ∫ x, (f x).trace ∂μ = (∫ x, f x ∂μ).trace := by
  let L : Matrix m m ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap m ℂ ℂ)
  exact L.integral_comp_comm hf

def MM {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ∫ U, ff S U ∂(QAlgorithms.Schur.unitaryHaar d)

lemma X7N2_MM_comm {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (V : G d) :
    MM S * KK (V : Matrix (Fin d) (Fin d) ℂ) = KK (V : Matrix (Fin d) (Fin d) ℂ) * MM S := by
  have hinv : (KK (V : Matrix (Fin d) (Fin d) ℂ))ᴴ * MM S * KK (V : Matrix (Fin d) (Fin d) ℂ) = MM S := by
    unfold MM
    rw [← X7N2_int_conj _ _ _ (X7N2_ff_int S)]
    have : ∀ U : G d, (KK (V : Matrix (Fin d) (Fin d) ℂ))ᴴ * ff S U * KK (V : Matrix (Fin d) (Fin d) ℂ)
        = ff S (U * V) := by
      intro U
      simp only [ff, Matrix.UnitaryGroup.mul_apply, X7N2_KK_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    simp_rw [this]
    exact X7N2_intRight d (ff S) V
  have hu := (X7N2_KK_unit V).2
  calc MM S * KK (V : Matrix (Fin d) (Fin d) ℂ)
      = (KK (V : Matrix (Fin d) (Fin d) ℂ) * (KK (V : Matrix (Fin d) (Fin d) ℂ))ᴴ) * MM S *
          KK (V : Matrix (Fin d) (Fin d) ℂ) := by rw [hu, Matrix.one_mul]
    _ = KK (V : Matrix (Fin d) (Fin d) ℂ) * ((KK (V : Matrix (Fin d) (Fin d) ℂ))ᴴ * MM S *
          KK (V : Matrix (Fin d) (Fin d) ℂ)) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hinv]

open QAlgorithms.Papers.Independent.Dependency50.P19 in
lemma X7N2_swap_KK {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : swap (Fin d) * KK U = KK U * swap (Fin d) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.mul_apply, swap, KK, Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]

lemma X7N2_tr_MM {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : (MM S).trace = S.trace := by
  unfold MM
  rw [← X7N2_int_trace _ (X7N2_ff_int S)]
  have : ∀ U : G d, (ff S U).trace = S.trace := by
    intro U
    simp only [ff]
    rw [Matrix.trace_mul_cycle, (X7N2_KK_unit U).2, Matrix.one_mul]
  simp [this]

open QAlgorithms.Papers.Independent.Dependency50.P19 in
lemma X7N2_tr_MMF {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (MM S * swap (Fin d)).trace = (S * swap (Fin d)).trace := by
  have h1 : MM S * swap (Fin d) = ∫ U, 1 * ff S U * swap (Fin d) ∂(QAlgorithms.Schur.unitaryHaar d) := by
    rw [X7N2_int_conj _ _ _ (X7N2_ff_int S), Matrix.one_mul]; rfl
  rw [h1, ← X7N2_int_trace]
  · have : ∀ U : G d, (1 * ff S U * swap (Fin d)).trace = (S * swap (Fin d)).trace := by
      intro U
      simp only [ff, Matrix.one_mul]
      have e : (KK (U : Matrix (Fin d) (Fin d) ℂ))ᴴ * S * KK (U : Matrix (Fin d) (Fin d) ℂ) * swap (Fin d)
          = (KK (U : Matrix (Fin d) (Fin d) ℂ))ᴴ * (S * swap (Fin d) * KK (U : Matrix (Fin d) (Fin d) ℂ)) := by
        rw [Matrix.mul_assoc _ (KK _), ← X7N2_swap_KK]; simp only [Matrix.mul_assoc]
      rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, (X7N2_KK_unit U).2, Matrix.mul_one]
    simp_rw [this]
    simp
  · exact (((continuous_const.matrix_mul (X7N2_ff_cont S)).matrix_mul continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

@[simp] lemma X7N2_and_symm {α : Type*} (a b : α) : (a = b ∧ b = a) ↔ a = b :=
  ⟨fun h => h.1, fun h => ⟨h, h.symm⟩⟩

open QAlgorithms.Papers.Independent.Dependency50.P19 in
lemma X7N2_trace_form {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (x y : ℂ)
    (h : ∀ i j k l : Fin d, M (i, j) (k, l) = (if i = k ∧ j = l then x else 0) + (if i = l ∧ j = k then y else 0)) :
    M.trace = (d : ℂ)^2 * x + d * y ∧ (M * swap (Fin d)).trace = d * x + (d : ℂ)^2 * y := by
  constructor
  · simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, h]
    simp [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
    ring
  · simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, h, swap]
    simp [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and, add_mul]
    ring

lemma X7N2_card2 {a1 a2 : ℕ} (b : Fin a2) :
    (Finset.univ.filter (fun q : Fin a1 × Fin a2 => b = q.2)).card = a1 := by
  simp only [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

lemma X7N2_card1 {a1 a2 : ℕ} (b : Fin a1) :
    (Finset.univ.filter (fun q : Fin a1 × Fin a2 => b = q.1)).card = a2 := by
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp
  · intro c _ hc; simp [Ne.symm hc]
  · simp

open QAlgorithms.Papers.Independent.Dependency50.P19 in
lemma X7N2_tr_S (a1 a2 : ℕ) : (swapSecond a1 a2).trace = (a1 : ℂ)^2 * a2 := by
  simp only [Matrix.trace, Matrix.diag, swapSecond, Fintype.sum_prod_type]
  rw [← (finProdFinEquiv (m := a1) (n := a2)).sum_comp]
  simp only [Equiv.symm_apply_apply]
  conv_lhs => arg 2; ext p; rw [← (finProdFinEquiv (m := a1) (n := a2)).sum_comp]
  simp [Fintype.sum_prod_type, X7N2_card2]
  ring

open QAlgorithms.Papers.Independent.Dependency50.P19 in
lemma X7N2_trF {X : Type*} [Fintype X] [DecidableEq X] (M : Matrix (X × X) (X × X) ℂ) :
    (M * swap X).trace = ∑ i, ∑ j, M (i, j) (j, i) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, swap, Fintype.sum_prod_type, mul_ite, mul_one,
    mul_zero, ite_and]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

open QAlgorithms.Papers.Independent.Dependency50.P19 in
lemma X7N2_tr_SF (a1 a2 : ℕ) : (swapSecond a1 a2 * swap (Fin (a1 * a2))).trace = (a1 : ℂ) * (a2 : ℂ)^2 := by
  rw [X7N2_trF]
  simp only [swapSecond]
  rw [← (finProdFinEquiv (m := a1) (n := a2)).sum_comp]
  simp only [Equiv.symm_apply_apply]
  conv_lhs => arg 2; ext p; rw [← (finProdFinEquiv (m := a1) (n := a2)).sum_comp]
  simp [Fintype.sum_prod_type, X7N2_card1]
  ring

lemma X7N2_int_kron {X : Type*} [MeasurableSpace X] {μ : Measure X} {m n : Type*} [Fintype m] [Fintype n]
    (f : X → Matrix m m ℂ) (C : Matrix n n ℂ) (hf : Integrable f μ) :
    ∫ x, Matrix.kronecker (f x) C ∂μ = Matrix.kronecker (∫ x, f x ∂μ) C := by
  let L0 : Matrix m m ℂ →ₗ[ℂ] Matrix (m × n) (m × n) ℂ :=
    { toFun := fun X => Matrix.kronecker X C
      map_add' := fun X Y => by simp [Matrix.kronecker, Matrix.add_kronecker]
      map_smul' := fun c X => by simp [Matrix.kronecker, Matrix.smul_kronecker] }
  let L : Matrix m m ℂ →L[ℂ] Matrix (m × n) (m × n) ℂ := LinearMap.toContinuousLinearMap L0
  exact L.integral_comp_comm hf

end X7N2

open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise
noncomputable section
namespace X7N2
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P19

lemma X7N2_MM_formula (a1 a2 : ℕ) (hd2 : 2 ≤ a1*a2) (i j k l : Fin (a1*a2)) :
    MM (swapSecond a1 a2) (i,j) (k,l) =
      (if i = k ∧ j = l then ((a2:ℂ)*((a1:ℂ)^2-1)/(((a1:ℂ)*a2)^2-1)) else 0) +
      (if i = l ∧ j = k then ((a1:ℂ)*((a2:ℂ)^2-1)/(((a1:ℂ)*a2)^2-1)) else 0) := by
  obtain ⟨x, y, hxy⟩ := X7N2_comm hd2 _ (X7N2_MM_comm (swapSecond a1 a2))
  obtain ⟨t1, t2⟩ := X7N2_trace_form _ x y hxy
  rw [X7N2_tr_MM, X7N2_tr_S] at t1
  rw [X7N2_tr_MMF, X7N2_tr_SF] at t2
  push_cast at t1 t2
  have hAB : (2 : ℝ) ≤ (a1 : ℝ) * a2 := by exact_mod_cast hd2
  have hc1 : ((a1 : ℂ) * a2 - 1) ≠ 0 := by
    intro h
    have : ((a1 : ℝ) * a2 - 1 : ℝ) = 0 := by exact_mod_cast h
    linarith
  have hc2 : ((a1 : ℂ) * a2 + 1) ≠ 0 := by
    intro h
    have : ((a1 : ℝ) * a2 + 1 : ℝ) = 0 := by exact_mod_cast h
    linarith
  have hc0 : ((a1 : ℂ) * a2) ≠ 0 := by
    intro h
    have : ((a1 : ℝ) * a2 : ℝ) = 0 := by exact_mod_cast h
    linarith
  have hc3 : ((a1 : ℂ) * a2)^2 - 1 ≠ 0 := by
    have : ((a1 : ℂ) * a2)^2 - 1 = ((a1 : ℂ) * a2 - 1) * ((a1 : ℂ) * a2 + 1) := by ring
    rw [this]; exact mul_ne_zero hc1 hc2
  have hx : x = a2 * (a1^2 - 1) / (((a1 : ℂ) * a2)^2 - 1) := by
    rw [eq_div_iff hc3]
    apply mul_left_cancel₀ hc0
    linear_combination t2 - ((a1 : ℂ) * a2) * t1
  have hy : y = a1 * (a2^2 - 1) / (((a1 : ℂ) * a2)^2 - 1) := by
    rw [eq_div_iff hc3]
    apply mul_left_cancel₀ hc0
    linear_combination t1 - ((a1 : ℂ) * a2) * t2
  rw [hxy, hx, hy]

def Ψ {a1 a2 : ℕ} (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ) (a b c e : Fin (a1*a2)) : ℂ :=
  ∑ k : Fin a1, ∑ i : Fin a2, ∑ k' : Fin a1, ∑ j : Fin a2,
    U (finProdFinEquiv (k,i)) a * U (finProdFinEquiv (k',j)) c *
      conj (U (finProdFinEquiv (k,j)) b) * conj (U (finProdFinEquiv (k',i)) e)

lemma X7N2_S_sum (a1 a2 : ℕ) (g : Fin (a1*a2) → Fin (a1*a2) → Fin (a1*a2) → Fin (a1*a2) → ℂ) :
    ∑ p, ∑ q, ∑ p', ∑ q', swapSecond a1 a2 (p,q) (p',q') * g p q p' q' =
    ∑ k : Fin a1, ∑ i : Fin a2, ∑ k' : Fin a1, ∑ j : Fin a2,
      g (finProdFinEquiv (k,i)) (finProdFinEquiv (k',j)) (finProdFinEquiv (k,j)) (finProdFinEquiv (k',i)) := by
  simp only [swapSecond]
  rw [← (finProdFinEquiv (m := a1) (n := a2)).sum_comp]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [← (finProdFinEquiv (m := a1) (n := a2)).sum_comp]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← (finProdFinEquiv (m := a1) (n := a2)).sum_comp]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single k, Finset.sum_eq_single j]
  · rw [← (finProdFinEquiv (m := a1) (n := a2)).sum_comp]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single k', Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · intro b _ hb
    apply Finset.sum_eq_zero; intro q' _
    simp [Ne.symm hb]
  · simp
  · intro b _ hb
    apply Finset.sum_eq_zero; intro m _
    apply Finset.sum_eq_zero; intro q' _
    simp [Ne.symm hb]
  · simp

lemma X7N2_sum4 {X : Type*} [Fintype X] (f : X → X → X → X → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

lemma X7N2_S_conj (a1 a2 : ℕ) (x y : Fin (a1*a2) × Fin (a1*a2)) :
    conj (swapSecond a1 a2 x y) = swapSecond a1 a2 x y := by
  simp only [swapSecond]; split_ifs <;> simp

lemma X7N2_Ψ_eq {a1 a2 : ℕ} (U : G (a1*a2)) (a b c e : Fin (a1*a2)) :
    Ψ (U : Matrix _ _ ℂ) a b c e = conj (ff (swapSecond a1 a2) U (a,c) (b,e)) := by
  rw [Ψ, ← X7N2_S_sum a1 a2 (fun p q p' q' => (U : Matrix _ _ ℂ) p a * (U : Matrix _ _ ℂ) q c *
    conj ((U : Matrix _ _ ℂ) p' b) * conj ((U : Matrix _ _ ℂ) q' e))]
  simp only [ff, KK, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, map_sum, map_mul, Finset.sum_mul, star_mul',
    RCLike.star_def, Complex.conj_conj]
  rw [X7N2_sum4]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun p' _ => Finset.sum_congr rfl fun q' _ => ?_
  rw [X7N2_S_conj]; ring

lemma X7N2_trA {R : Type*} [Fintype R] {a1 a2 : ℕ} (ρ : Matrix (R × Fin (a1*a2)) (R × Fin (a1*a2)) ℂ)
    (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ) :
    ((sigma a1 a2 ρ U) * (sigma a1 a2 ρ U)).trace = ∑ a, ∑ b, ∑ c, ∑ e,
      (∑ r, ∑ r', ρ (r,a) (r',b) * ρ (r',c) (r,e)) * Ψ U a b c e := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, sigma, Ψ, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun ⟨r,i,r',j,k',c,e,k,a,b⟩ => ⟨a,b,c,e,k,i,k',j,r,r'⟩
      invFun := fun ⟨a,b,c,e,k,i,k',j,r,r'⟩ => ⟨r,i,r',j,k',c,e,k,a,b⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ (fun x => ?_)
  obtain ⟨r,i,r',j,k',c,e,k,a,b⟩ := x
  simp only [Equiv.coe_fn_mk]
  ring

lemma X7N2_trB {R : Type*} [Fintype R] {a1 a2 : ℕ} (ρ : Matrix (R × Fin (a1*a2)) (R × Fin (a1*a2)) ℂ)
    (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ) (P : Matrix R R ℂ) :
    ((sigma a1 a2 ρ U) * Matrix.kronecker P (traceLeft (sigma a1 a2 ρ U))).trace = ∑ a, ∑ b, ∑ c, ∑ e,
      (∑ r, ∑ r', ∑ s, ρ (r,a) (r',b) * P r' r * ρ (s,c) (s,e)) * Ψ U a b c e := by
  have h1 : ((sigma a1 a2 ρ U) * Matrix.kronecker P (traceLeft (sigma a1 a2 ρ U))).trace =
      ∑ r, ∑ i, ∑ r', ∑ j, sigma a1 a2 ρ U (r,i) (r',j) * (P r' r * ∑ s, sigma a1 a2 ρ U (s,j) (s,i)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
    rfl
  rw [h1]
  simp (config := {maxSteps := 4000000}) only [sigma, Ψ, Finset.sum_mul, Finset.mul_sum]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun ⟨r,i,r',j,s,k',c,e,k,a,b⟩ => ⟨a,b,c,e,k,i,k',j,r,r',s⟩
      invFun := fun ⟨a,b,c,e,k,i,k',j,r,r',s⟩ => ⟨r,i,r',j,s,k',c,e,k,a,b⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ (fun x => ?_)
  obtain ⟨r,i,r',j,s,k',c,e,k,a,b⟩ := x
  simp only [Equiv.coe_fn_mk]
  ring

lemma X7N2_trC {R : Type*} [Fintype R] {a1 a2 : ℕ} (ρ : Matrix (R × Fin (a1*a2)) (R × Fin (a1*a2)) ℂ)
    (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ) :
    ((traceLeft (sigma a1 a2 ρ U)) * (traceLeft (sigma a1 a2 ρ U))).trace = ∑ a, ∑ b, ∑ c, ∑ e,
      (∑ r, ∑ s, ρ (r,a) (r,b) * ρ (s,c) (s,e)) * Ψ U a b c e := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, sigma, Ψ, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum, traceLeft, Matrix.of_apply]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun ⟨i,j,s,k',c,e,r,k,a,b⟩ => ⟨a,b,c,e,k,i,k',j,r,s⟩
      invFun := fun ⟨a,b,c,e,k,i,k',j,r,s⟩ => ⟨i,j,s,k',c,e,r,k,a,b⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ (fun x => ?_)
  obtain ⟨i,j,s,k',c,e,r,k,a,b⟩ := x
  simp only [Equiv.coe_fn_mk]
  ring

end X7N2

open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise
noncomputable section
namespace X7N2
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P19

lemma X7N2_unit_sum {a1 a2 : ℕ} (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ) (hU : Uᴴ * U = 1)
    (a b : Fin (a1*a2)) :
    ∑ k : Fin a1, ∑ i : Fin a2, U (finProdFinEquiv (k,i)) a * conj (U (finProdFinEquiv (k,i)) b) =
      if a = b then 1 else 0 := by
  have h := congrFun (congrFun hU b) a
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [← Fintype.sum_prod_type' (f := fun k i => U (finProdFinEquiv (k,i)) a * conj (U (finProdFinEquiv (k,i)) b)),
    (finProdFinEquiv (m := a1) (n := a2)).sum_comp (fun p => U p a * conj (U p b))]
  by_cases hab : a = b
  · subst hab; simp only [if_true] at h ⊢; rw [← h]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [Matrix.conjTranspose_apply, mul_comm]
  · rw [if_neg (Ne.symm hab)] at h; rw [if_neg hab, ← h]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [Matrix.conjTranspose_apply, mul_comm]

lemma X7N2_trR {R : Type*} [Fintype R] {a1 a2 : ℕ} (ρ : Matrix (R × Fin (a1*a2)) (R × Fin (a1*a2)) ℂ)
    (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ) (hU : Uᴴ * U = 1) :
    traceRight (sigma a1 a2 ρ U) = traceRight ρ := by
  ext r r'
  simp only [traceRight, Matrix.of_apply, sigma]
  have e1 : ∑ a, ρ (r,a) (r',a) = ∑ a, ∑ b, ρ (r,a) (r',b) *
      ∑ k : Fin a1, ∑ i : Fin a2, U (finProdFinEquiv (k,i)) a * conj (U (finProdFinEquiv (k,i)) b) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp_rw [X7N2_unit_sum U hU]
    simp
  rw [e1]
  simp only [Finset.mul_sum, Finset.sum_mul]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun ⟨i,k,a,b⟩ => ⟨a,b,k,i⟩
      invFun := fun ⟨a,b,k,i⟩ => ⟨i,k,a,b⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ (fun x => ?_)
  obtain ⟨i,k,a,b⟩ := x
  simp only [Equiv.coe_fn_mk]
  ring

lemma X7N2_sig_herm {R : Type*} [Fintype R] {a1 a2 : ℕ} (ρ : Matrix (R × Fin (a1*a2)) (R × Fin (a1*a2)) ℂ)
    (hρ : ∀ x y, star (ρ x y) = ρ y x) (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ) :
    (sigma a1 a2 ρ U)ᴴ = sigma a1 a2 ρ U := by
  ext ⟨r,i⟩ ⟨r',j⟩
  simp only [Matrix.conjTranspose_apply, sigma, star_sum, star_mul', hρ, RCLike.star_def, Complex.conj_conj]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma X7N2_frob_sq {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℂ) :
    frobNorm X ^ 2 = (X * Xᴴ).trace.re := by
  unfold frobNorm
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  norm_cast

lemma X7N2_trR_herm {α β : Type*} [Fintype β] (X : Matrix (α × β) (α × β) ℂ)
    (hX : ∀ x y, star (X x y) = X y x) : ∀ x y, star (traceRight X x y) = traceRight X y x := by
  intro x y; simp [traceRight, star_sum, hX]

lemma X7N2_trL_herm {α β : Type*} [Fintype α] (X : Matrix (α × β) (α × β) ℂ)
    (hX : ∀ x y, star (X x y) = X y x) : ∀ x y, star (traceLeft X x y) = traceLeft X y x := by
  intro x y; simp [traceLeft, star_sum, hX]

def TT {R : Type*} [Fintype R] {a1 a2 : ℕ} (ρ : Matrix (R × Fin (a1*a2)) (R × Fin (a1*a2)) ℂ)
    (a b c e : Fin (a1*a2)) : ℂ :=
  (∑ r, ∑ r', ρ (r,a) (r',b) * ρ (r',c) (r,e)) -
    2 * (∑ r, ∑ r', ∑ s, ρ (r,a) (r',b) * traceRight ρ r' r * ρ (s,c) (s,e)) +
    (traceRight ρ * traceRight ρ).trace * (∑ r, ∑ s, ρ (r,a) (r,b) * ρ (s,c) (s,e))

lemma X7N2_point {R : Type*} [Fintype R] {a1 a2 : ℕ} (ρ : Matrix (R × Fin (a1*a2)) (R × Fin (a1*a2)) ℂ)
    (hρ : ∀ x y, star (ρ x y) = ρ y x) (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ) (hU : Uᴴ * U = 1) :
    frobNorm (decouplingDifference a1 a2 ρ U) ^ 2 =
      (∑ a, ∑ b, ∑ c, ∑ e, TT ρ a b c e * Ψ U a b c e).re := by
  rw [X7N2_frob_sq]
  simp only [decouplingDifference]
  rw [X7N2_trR ρ U hU]
  set σ := sigma a1 a2 ρ U with hσ
  have hK : (Matrix.kronecker (traceRight ρ) (traceLeft σ))ᴴ = Matrix.kronecker (traceRight ρ) (traceLeft σ) := by
    have h1 : (traceRight ρ)ᴴ = traceRight ρ := by
      ext x y; simp [Matrix.conjTranspose_apply, X7N2_trR_herm ρ hρ]
    have h2 : (traceLeft σ)ᴴ = traceLeft σ := by
      have hs : ∀ x y, star (σ x y) = σ y x := by
        intro x y; rw [← Matrix.conjTranspose_apply, hσ, X7N2_sig_herm ρ hρ]
      ext x y; simp [Matrix.conjTranspose_apply, X7N2_trL_herm σ hs]
    simp only [Matrix.kronecker]
    rw [Matrix.conjTranspose_kronecker, h1, h2]
  rw [Matrix.conjTranspose_sub, hK, hσ, X7N2_sig_herm ρ hρ, ← hσ]
  congr 1
  rw [sub_mul, mul_sub, mul_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_mul_comm (Matrix.kronecker _ _) σ]
  have hKK : (Matrix.kronecker (traceRight ρ) (traceLeft σ) * Matrix.kronecker (traceRight ρ) (traceLeft σ)).trace
      = (traceRight ρ * traceRight ρ).trace * (traceLeft σ * traceLeft σ).trace := by
    simp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
  rw [hKK, hσ, X7N2_trA, X7N2_trB, X7N2_trC]
  have e : ∀ a b c e, TT ρ a b c e * Ψ U a b c e =
      (∑ r, ∑ r', ρ (r,a) (r',b) * ρ (r',c) (r,e)) * Ψ U a b c e -
      2 * ((∑ r, ∑ r', ∑ s, ρ (r,a) (r',b) * traceRight ρ r' r * ρ (s,c) (s,e)) * Ψ U a b c e) +
      (traceRight ρ * traceRight ρ).trace * ((∑ r, ∑ s, ρ (r,a) (r,b) * ρ (s,c) (s,e)) * Ψ U a b c e) := by
    intro a b c e; simp only [TT]; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end X7N2

open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise
noncomputable section
namespace X7N2
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P19

section
variable {R : Type*} [Fintype R] {d : ℕ} (ρ : Matrix (R × Fin d) (R × Fin d) ℂ)

lemma X7N2_X1 : ∑ a, ∑ c, ∑ r, ∑ r', ρ (r,a) (r',a) * ρ (r',c) (r,c) = (traceRight ρ * traceRight ρ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, traceRight, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun ⟨a,c,r,r'⟩ => ⟨r,r',c,a⟩
      invFun := fun ⟨r,r',c,a⟩ => ⟨a,c,r,r'⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ (fun x => ?_)
  obtain ⟨a,c,r,r'⟩ := x
  simp only [Equiv.coe_fn_mk]
  try ring

lemma X7N2_Y1 : ∑ a, ∑ c, ∑ r, ∑ r', ∑ s, ρ (r,a) (r',a) * traceRight ρ r' r * ρ (s,c) (s,c) =
    (traceRight ρ * traceRight ρ).trace * ρ.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, traceRight, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul,
    Fintype.sum_prod_type]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun ⟨a,c,r,r',s,h⟩ => ⟨s,c,r,r',h,a⟩
      invFun := fun ⟨s,c,r,r',h,a⟩ => ⟨a,c,r,r',s,h⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ (fun x => ?_)
  obtain ⟨a,c,r,r',s,h⟩ := x
  simp only [Equiv.coe_fn_mk]
  try ring

lemma X7N2_Z1 : ∑ a, ∑ c, ∑ r, ∑ s, ρ (r,a) (r,a) * ρ (s,c) (s,c) = ρ.trace * ρ.trace := by
  simp only [Matrix.trace, Matrix.diag, Finset.mul_sum, Finset.sum_mul, Fintype.sum_prod_type]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun ⟨a,c,r,s⟩ => ⟨s,c,r,a⟩
      invFun := fun ⟨s,c,r,a⟩ => ⟨a,c,r,s⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ (fun x => ?_)
  obtain ⟨a,c,r,s⟩ := x
  simp only [Equiv.coe_fn_mk]
  try ring

lemma X7N2_X2 : ∑ a, ∑ c, ∑ r, ∑ r', ρ (r,a) (r',c) * ρ (r',c) (r,a) = (ρ * ρ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, Fintype.sum_prod_type]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun ⟨a,c,r,r'⟩ => ⟨r,a,r',c⟩
      invFun := fun ⟨r,a,r',c⟩ => ⟨a,c,r,r'⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ (fun x => ?_)
  obtain ⟨a,c,r,r'⟩ := x
  simp only [Equiv.coe_fn_mk]
  try ring

lemma X7N2_Y2 : ∑ a, ∑ c, ∑ r, ∑ r', ∑ s, ρ (r,a) (r',c) * traceRight ρ r' r * ρ (s,c) (s,a) =
    (ρ * Matrix.kronecker (traceRight ρ) (traceLeft ρ)).trace := by
  have h1 : (ρ * Matrix.kronecker (traceRight ρ) (traceLeft ρ)).trace =
      ∑ r, ∑ a, ∑ r', ∑ c, ρ (r,a) (r',c) * (traceRight ρ r' r * ∑ s, ρ (s,c) (s,a)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
    rfl
  rw [h1]
  simp only [Finset.mul_sum, Finset.sum_mul]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun ⟨a,c,r,r',s⟩ => ⟨r,a,r',c,s⟩
      invFun := fun ⟨r,a,r',c,s⟩ => ⟨a,c,r,r',s⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ (fun x => ?_)
  obtain ⟨a,c,r,r',s⟩ := x
  simp only [Equiv.coe_fn_mk]
  try ring

lemma X7N2_Z2 : ∑ a, ∑ c, ∑ r, ∑ s, ρ (r,a) (r,c) * ρ (s,c) (s,a) = (traceLeft ρ * traceLeft ρ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, traceLeft, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun ⟨a,c,r,s⟩ => ⟨a,c,s,r⟩
      invFun := fun ⟨a,c,s,r⟩ => ⟨a,c,r,s⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ (fun x => ?_)
  obtain ⟨a,c,r,s⟩ := x
  simp only [Equiv.coe_fn_mk]
  try ring
end

end X7N2

open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise
noncomputable section
namespace X7N2
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P19

lemma X7N2_TT1 {R : Type*} [Fintype R] {a1 a2 : ℕ} (ρ : Matrix (R × Fin (a1*a2)) (R × Fin (a1*a2)) ℂ) :
    ∑ a, ∑ c, TT ρ a a c c = (traceRight ρ * traceRight ρ).trace -
      2 * ((traceRight ρ * traceRight ρ).trace * ρ.trace) + (traceRight ρ * traceRight ρ).trace * (ρ.trace * ρ.trace) := by
  have e : ∑ a, ∑ c, TT ρ a a c c = (∑ a, ∑ c, ∑ r, ∑ r', ρ (r,a) (r',a) * ρ (r',c) (r,c)) -
      2 * (∑ a, ∑ c, ∑ r, ∑ r', ∑ s, ρ (r,a) (r',a) * traceRight ρ r' r * ρ (s,c) (s,c)) +
      (traceRight ρ * traceRight ρ).trace * (∑ a, ∑ c, ∑ r, ∑ s, ρ (r,a) (r,a) * ρ (s,c) (s,c)) := by
    simp only [TT, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [e, X7N2_X1, X7N2_Y1, X7N2_Z1]

lemma X7N2_TT2 {R : Type*} [Fintype R] {a1 a2 : ℕ} (ρ : Matrix (R × Fin (a1*a2)) (R × Fin (a1*a2)) ℂ) :
    ∑ a, ∑ c, TT ρ a c c a = (ρ * ρ).trace -
      2 * (ρ * Matrix.kronecker (traceRight ρ) (traceLeft ρ)).trace +
      (traceRight ρ * traceRight ρ).trace * (traceLeft ρ * traceLeft ρ).trace := by
  have e : ∑ a, ∑ c, TT ρ a c c a = (∑ a, ∑ c, ∑ r, ∑ r', ρ (r,a) (r',c) * ρ (r',c) (r,a)) -
      2 * (∑ a, ∑ c, ∑ r, ∑ r', ∑ s, ρ (r,a) (r',c) * traceRight ρ r' r * ρ (s,c) (s,a)) +
      (traceRight ρ * traceRight ρ).trace * (∑ a, ∑ c, ∑ r, ∑ s, ρ (r,a) (r,c) * ρ (s,c) (s,a)) := by
    simp only [TT, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [e, X7N2_X2, X7N2_Y2, X7N2_Z2]

lemma X7N2_int {R : Type*} [Fintype R] {a1 a2 : ℕ} (ρ : Matrix (R × Fin (a1*a2)) (R × Fin (a1*a2)) ℂ) :
    ∫ U : G (a1*a2), (∑ a, ∑ b, ∑ c, ∑ e, TT ρ a b c e * Ψ (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ) a b c e).re
      ∂(Schur.unitaryHaar (a1*a2)) =
    (∑ a, ∑ b, ∑ c, ∑ e, TT ρ a b c e * conj (MM (swapSecond a1 a2) (a,c) (b,e))).re := by
  have hc : ∀ a b c e, Continuous (fun U : G (a1*a2) => Ψ (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ) a b c e) := by
    intro a b c e
    rw [funext (fun U : G (a1*a2) => X7N2_Ψ_eq (a1 := a1) (a2 := a2) U a b c e)]
    exact Complex.continuous_conj.comp ((X7N2_ff_cont _).matrix_elem _ _)
  have hI : ∀ f : G (a1*a2) → ℂ, Continuous f → Integrable f (Schur.unitaryHaar (a1*a2)) :=
    fun f hf => hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hv : ∀ a b c e, ∫ U, Ψ (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ) a b c e ∂(Schur.unitaryHaar (a1*a2)) =
      conj (MM (swapSecond a1 a2) (a,c) (b,e)) := by
    intro a b c e
    rw [funext (fun U : G (a1*a2) => X7N2_Ψ_eq (a1 := a1) (a2 := a2) U a b c e), integral_conj, MM, X7N2_entry' _ (X7N2_ff_int _)]
  have hre := integral_re (𝕜 := ℂ) (hI (fun U : G (a1*a2) =>
      ∑ a, ∑ b, ∑ c, ∑ e, TT ρ a b c e * Ψ (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ) a b c e) (by fun_prop))
  simp only [RCLike.re_to_complex] at hre
  rw [hre]
  congr 1
  rw [integral_finset_sum _ (fun a _ => hI _ (by fun_prop))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finset_sum _ (fun b _ => hI _ (by fun_prop))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_finset_sum _ (fun c _ => hI _ (by fun_prop))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_finset_sum _ (fun e _ => hI _ (by fun_prop))]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [integral_const_mul, hv]

lemma X7N2_herm_im {m : Type*} [Fintype m] (X : Matrix m m ℂ) (hX : ∀ x y, star (X x y) = X y x) :
    (X * X).trace.im = 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.im_sum]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [← hX i j, RCLike.star_def, Complex.mul_conj]
  simp

end X7N2

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise
attribute [local instance] Classical.propDecidable Classical.decEq

open MeasureTheory QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P19 X7N2
  QAlgorithms.Papers.Independent.Information100.P32 in
theorem solution {R B : Type*} [Fintype R] [Fintype B]
    [DecidableEq R] [DecidableEq B] [Nonempty R] [Nonempty B]
    (a1 a2 : ℕ) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (psi : EuclideanSpace ℂ (R × (Fin (a1*a2) × B))) (hpsi : IsState psi) :
    (∫ U : Matrix.unitaryGroup (Fin (a1*a2)) ℂ,
      (frobNorm (decouplingDifference a1 a2 (marginalRA (pureDensity psi))
        (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ)))^2 ∂(Schur.unitaryHaar (a1*a2))) =
    (((a1 : ℝ)*(a2 : ℝ)^2-(a1 : ℝ))/(((a1*a2 : ℕ) : ℝ)^2-1)) *
      (purity (marginalRA (pureDensity psi)) -
       2 * ((marginalRA (pureDensity psi)) * Matrix.kronecker
         (traceRight (marginalRA (pureDensity psi)))
         (traceLeft (marginalRA (pureDensity psi)))).trace.re +
       purity (traceLeft (marginalRA (pureDensity psi))) *
         purity (traceRight (marginalRA (pureDensity psi)))) := by
  have hρ : ∀ x y, star (marginalRA (pureDensity psi) x y) = marginalRA (pureDensity psi) y x := by
    intro x y
    simp only [marginalRA, idTensorSuperop, traceRight, pureDensity, Matrix.of_apply, star_sum, star_mul',
      RCLike.star_def, Complex.conj_conj]
    refine Finset.sum_congr rfl fun h _ => ?_
    ring
  have htr : (marginalRA (pureDensity psi)).trace = 1 := by
    have h1 : (marginalRA (pureDensity psi)).trace =
        ∑ x : R × (Fin (a1*a2) × B), ((‖psi x‖ ^ 2 : ℝ) : ℂ) := by
      simp only [marginalRA, idTensorSuperop, traceRight, pureDensity, Matrix.trace, Matrix.diag,
        Matrix.of_apply, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun h _ => ?_
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [h1, ← Complex.ofReal_sum]
    have h2 := hpsi
    unfold IsState at h2
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h2
    rw [h2, Complex.ofReal_one]
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun U : Matrix.unitaryGroup (Fin (a1*a2)) ℂ =>
    X7N2_point _ hρ (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ) (Matrix.UnitaryGroup.star_mul_self U)))]
  rw [X7N2_int]
  have hR := X7N2_trR_herm _ hρ
  have hL := X7N2_trL_herm _ hρ
  generalize marginalRA (pureDensity psi) = ρ at hρ htr hR hL ⊢
  have hT1 : ∑ a, ∑ c, TT ρ a a c c = 0 := by rw [X7N2_TT1, htr]; ring
  rcases Nat.lt_or_ge (a1*a2) 2 with hlt | hd2
  · have h1 : a1 * a2 = 1 := by
      have : 0 < a1 * a2 := Nat.mul_pos ha1 ha2
      omega
    have ha1' : a1 = 1 := Nat.eq_one_of_mul_eq_one_right h1
    have ha2' : a2 = 1 := Nat.eq_one_of_mul_eq_one_left h1
    subst ha1' ha2'
    haveI : Subsingleton (Fin (1*1)) := ⟨fun a b => Fin.ext (by omega)⟩
    have hM : ∀ a b c e : Fin (1*1), conj (MM (swapSecond 1 1) (a,c) (b,e)) = 1 := by
      intro a b c e
      have htr' := X7N2_tr_MM (swapSecond 1 1)
      rw [X7N2_tr_S] at htr'
      have : (MM (swapSecond 1 1)).trace = MM (swapSecond 1 1) (a,c) (a,c) := by
        simp only [Matrix.trace, Matrix.diag]
        exact Fintype.sum_subsingleton _ (a,c)
      rw [this] at htr'
      rw [Subsingleton.elim b a, Subsingleton.elim e c, htr']
      simp
    simp only [hM, mul_one]
    have : ∑ a : Fin (1*1), ∑ b : Fin (1*1), ∑ c : Fin (1*1), ∑ e : Fin (1*1), TT ρ a b c e =
        ∑ a, ∑ c, TT ρ a a c c := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Fintype.sum_subsingleton _ a]
      refine Finset.sum_congr rfl fun c _ => ?_
      exact Fintype.sum_subsingleton _ c
    rw [this, hT1]
    simp
  · set xr : ℝ := (a2:ℝ)*((a1:ℝ)^2-1)/(((a1:ℝ)*a2)^2-1) with hxr
    set yr : ℝ := (a1:ℝ)*((a2:ℝ)^2-1)/(((a1:ℝ)*a2)^2-1) with hyr
    have hM : ∀ a b c e, conj (MM (swapSecond a1 a2) (a,c) (b,e)) =
        (if a = b ∧ c = e then (xr : ℂ) else 0) + (if a = e ∧ c = b then (yr : ℂ) else 0) := by
      intro a b c e
      rw [X7N2_MM_formula _ _ hd2, hxr, hyr]
      split_ifs <;> simp [map_div₀]
    simp only [hM]
    have hsplit : ∑ a, ∑ b, ∑ c, ∑ e, TT ρ a b c e *
        ((if a = b ∧ c = e then (xr : ℂ) else 0) + (if a = e ∧ c = b then (yr : ℂ) else 0)) =
        (xr : ℂ) * ∑ a, ∑ c, TT ρ a a c c + (yr : ℂ) * ∑ a, ∑ c, TT ρ a c c a := by
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, ite_and, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
        simp only [if_true]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp [mul_comm]
      · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
        ring
    rw [hsplit, hT1, X7N2_TT2, mul_zero, zero_add, Complex.re_ofReal_mul]
    have hy : yr = ((a1 : ℝ)*(a2 : ℝ)^2-(a1 : ℝ))/(((a1*a2 : ℕ) : ℝ)^2-1) := by
      rw [hyr]; push_cast; ring
    rw [hy]
    congr 1
    simp only [purity, Complex.sub_re, Complex.add_re, Complex.mul_re, X7N2_herm_im _ hR, X7N2_herm_im _ hL]
    simp only [Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero, zero_mul]
    ring
