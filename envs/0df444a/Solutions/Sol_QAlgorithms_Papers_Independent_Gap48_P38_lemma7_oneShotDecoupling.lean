-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P38.lemma7_oneShotDecoupling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T13:36:08.089488+00:00
-- url     : https://prove2.me/submissions/3836777c-566c-482a-93c3-c461eb77e975

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P38

open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

noncomputable section
namespace X7L7

attribute [local instance] Classical.propDecidable Classical.decEq

def swap (X : Type*) [DecidableEq X] : Matrix (X × X) (X × X) ℂ :=
  fun i j => if i.1 = j.2 ∧ i.2 = j.1 then 1 else 0
noncomputable instance X7L7_cen {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) := SeminormedAddGroup.toContinuousENorm

instance X7L7_haar (d : ℕ) : (QAlgorithms.Schur.unitaryHaar d).IsHaarMeasure := by
  unfold QAlgorithms.Schur.unitaryHaar; infer_instance

abbrev G (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ

def KK {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.kronecker U U

def ff {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (U : G d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (KK (U : Matrix (Fin d) (Fin d) ℂ))ᴴ * S * KK (U : Matrix (Fin d) (Fin d) ℂ)

lemma X7L7_KK_cont (d : ℕ) : Continuous (fun U : G d => KK (U : Matrix (Fin d) (Fin d) ℂ)) := by
  have hU : Continuous (fun U : G d => (U : Matrix (Fin d) (Fin d) ℂ)) := continuous_subtype_val
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [KK]
  exact (hU.matrix_elem i.1 j.1).mul (hU.matrix_elem i.2 j.2)

lemma X7L7_ff_cont {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Continuous (ff S) := by
  unfold ff
  exact ((X7L7_KK_cont d).matrix_conjTranspose.matrix_mul continuous_const).matrix_mul (X7L7_KK_cont d)

lemma X7L7_ff_int {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Integrable (ff S) (QAlgorithms.Schur.unitaryHaar d) :=
  (X7L7_ff_cont S).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma X7L7_KK_mul {d : ℕ} (U V : Matrix (Fin d) (Fin d) ℂ) : KK (U * V) = KK U * KK V := by
  unfold KK; simp only [Matrix.kronecker]; rw [Matrix.mul_kronecker_mul]

lemma X7L7_KK_unit {d : ℕ} (U : G d) : (KK (U : Matrix (Fin d) (Fin d) ℂ))ᴴ * KK (U : Matrix (Fin d) (Fin d) ℂ) = 1 ∧
    KK (U : Matrix (Fin d) (Fin d) ℂ) * (KK (U : Matrix (Fin d) (Fin d) ℂ))ᴴ = 1 := by
  have h1 : (U : Matrix (Fin d) (Fin d) ℂ)ᴴ * U = 1 := Matrix.UnitaryGroup.star_mul_self U
  have h2 : (U : Matrix (Fin d) (Fin d) ℂ) * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp U.2
    rwa [Matrix.star_eq_conjTranspose] at this
  unfold KK
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, h1, h2]
  simp


lemma X7L7_phase_aux {X : Type*} [DecidableEq X] (a b c e : X)
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

lemma X7L7_diag_unit {d : ℕ} (s : Fin d) :
    Matrix.diagonal (fun t : Fin d => if t = s then Complex.I else 1) ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1; funext t
  by_cases h : t = s <;> simp [h]

lemma X7L7_phase {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : ∀ V : G d, M * KK (V : Matrix (Fin d) (Fin d) ℂ) = KK (V : Matrix (Fin d) (Fin d) ℂ) * M)
    (i j k l : Fin d) (hne : M (i, j) (k, l) ≠ 0) : (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  apply X7L7_phase_aux
  intro s
  have := congrFun (congrFun (hM ⟨_, X7L7_diag_unit s⟩) (i, j)) (k, l)
  simp only [KK, Matrix.kronecker, Matrix.diagonal_kronecker_diagonal, Matrix.mul_diagonal,
    Matrix.diagonal_mul] at this
  have := mul_left_cancel₀ hne (this.trans (mul_comm _ _))
  exact this.symm

def Pm {d : ℕ} (σ : Equiv.Perm (Fin d)) : Matrix (Fin d) (Fin d) ℂ := fun a b => if a = σ b then 1 else 0

lemma X7L7_Pm_unit {d : ℕ} (σ : Equiv.Perm (Fin d)) : Pm σ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
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

lemma X7L7_perm {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : ∀ V : G d, M * KK (V : Matrix (Fin d) (Fin d) ℂ) = KK (V : Matrix (Fin d) (Fin d) ℂ) * M)
    (σ : Equiv.Perm (Fin d)) (a b c e : Fin d) : M (σ a, σ b) (σ c, σ e) = M (a, b) (c, e) := by
  have := congrFun (congrFun (hM ⟨_, X7L7_Pm_unit σ⟩) (σ a, σ b)) (c, e)
  simp only [KK, Matrix.kronecker, Matrix.mul_apply, Matrix.kroneckerMap_apply, Pm,
    Fintype.sum_prod_type] at this
  simp [ite_mul, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq] at this
  exact this

def ww {d : ℕ} (i0 i1 : Fin d) : Fin d → ℂ := fun k => if k = i0 then 3/5 else if k = i1 then 4/5 else 0

def Hh {d : ℕ} (i0 i1 : Fin d) : Matrix (Fin d) (Fin d) ℂ := 1 - (2 : ℂ) • Matrix.vecMulVec (ww i0 i1) (ww i0 i1)

lemma X7L7_ww_star {d : ℕ} (i0 i1 : Fin d) : star (ww i0 i1) = ww i0 i1 := by
  funext k; simp only [Pi.star_apply, ww]; split_ifs <;> simp

lemma X7L7_ww_dot {d : ℕ} (i0 i1 : Fin d) (h01 : i0 ≠ i1) : ww i0 i1 ⬝ᵥ ww i0 i1 = 1 := by
  have : ∀ k, ww i0 i1 k * ww i0 i1 k = (if k = i0 then (9/25 : ℂ) else 0) + (if k = i1 then (16/25 : ℂ) else 0) := by
    intro k; simp only [ww]
    by_cases h0 : k = i0
    · subst h0; simp [h01]; norm_num
    · by_cases h1 : k = i1
      · subst h1; simp [h0]; norm_num
      · simp [h0, h1]
  simp only [dotProduct, this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num

lemma X7L7_Hh_unit {d : ℕ} (i0 i1 : Fin d) (h01 : i0 ≠ i1) : Hh i0 i1 ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  have hP : (Matrix.vecMulVec (ww i0 i1) (ww i0 i1))ᴴ = Matrix.vecMulVec (ww i0 i1) (ww i0 i1) := by
    rw [Matrix.conjTranspose_vecMulVec, X7L7_ww_star]
  have hPP : Matrix.vecMulVec (ww i0 i1) (ww i0 i1) * Matrix.vecMulVec (ww i0 i1) (ww i0 i1) =
      Matrix.vecMulVec (ww i0 i1) (ww i0 i1) := by
    rw [Matrix.vecMulVec_mul_vecMulVec, X7L7_ww_dot i0 i1 h01, one_smul]
  unfold Hh
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hP, Matrix.conjTranspose_one]
  simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hPP, smul_smul]
  have h2 : star (2 : ℂ) = 2 := by simp
  rw [h2]
  module

lemma X7L7_house {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : ∀ V : G d, M * KK (V : Matrix (Fin d) (Fin d) ℂ) = KK (V : Matrix (Fin d) (Fin d) ℂ) * M)
    (i0 i1 : Fin d) (h01 : i0 ≠ i1) (z x y : ℂ)
    (hrow : ∀ q, M (i0, i0) q = if q = (i0, i0) then z else 0)
    (hcol : ∀ p, M p (i0, i1) = (if p = (i0, i1) then x else 0) + (if p = (i1, i0) then y else 0)) :
    z = x + y := by
  have := congrFun (congrFun (hM ⟨_, X7L7_Hh_unit i0 i1 h01⟩) (i0, i0)) (i0, i1)
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

lemma X7L7_pair {d : ℕ} (i0 i1 i j : Fin d) (h01 : i0 ≠ i1) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin d), σ i0 = i ∧ σ i1 = j := by
  refine ⟨(Equiv.swap i0 i).trans (Equiv.swap (Equiv.swap i0 i i1) j), ?_, ?_⟩
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]
    have : i ≠ Equiv.swap i0 i i1 := by
      intro h
      have : Equiv.swap i0 i i0 = Equiv.swap i0 i i1 := by rw [Equiv.swap_apply_left]; exact h
      exact h01 ((Equiv.swap i0 i).injective this)
    rw [Equiv.swap_apply_of_ne_of_ne this hij]
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]

theorem X7L7_comm {d : ℕ} (hd : 2 ≤ d) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
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
    have := X7L7_perm M hM (Equiv.swap i0 i) i0 i0 i0 i0
    simpa using this
  have hx : ∀ i j, i ≠ j → M (i, j) (i, j) = x := by
    intro i j hij
    obtain ⟨σ, h1, h2⟩ := X7L7_pair i0 i1 i j h01 hij
    have := X7L7_perm M hM σ i0 i1 i0 i1
    rwa [h1, h2] at this
  have hy : ∀ i j, i ≠ j → M (i, j) (j, i) = y := by
    intro i j hij
    obtain ⟨σ, h1, h2⟩ := X7L7_pair i0 i1 i j h01 hij
    have := X7L7_perm M hM σ i0 i1 i1 i0
    rwa [h1, h2] at this
  have hrow : ∀ q, M (i0, i0) q = if q = (i0, i0) then z else 0 := by
    rintro ⟨k, l⟩
    by_cases hq : (k, l) = (i0, i0)
    · rw [if_pos hq, hq]
    · rw [if_neg hq]
      by_contra hne
      rcases X7L7_phase M hM i0 i0 k l hne with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;>
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
        rcases X7L7_phase M hM k l i0 i1 hne with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
        · exact hq rfl
        · exact hq2 rfl
  have hz : z = x + y := X7L7_house M hM i0 i1 h01 z x y hrow hcol
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
      rcases X7L7_phase M hM i j k l hne with h | h
      · exact hA h
      · exact hB h

instance X7L7_prob (d : ℕ) : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

lemma X7L7_mapRight (d : ℕ) (g : G d) :
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

lemma X7L7_intRight (d : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : G d → E) (g : G d) :
    ∫ U, f (U * g) ∂(QAlgorithms.Schur.unitaryHaar d) = ∫ U, f U ∂(QAlgorithms.Schur.unitaryHaar d) := by
  have hm : MeasurableEmbedding (· * g : G d → G d) := (MeasurableEquiv.mulRight g).measurableEmbedding
  rw [← hm.integral_map, X7L7_mapRight]

lemma X7L7_entry' {X : Type*} [MeasurableSpace X] {μ : Measure X} {m n : Type*} [Fintype m] [Fintype n]
    (f : X → Matrix m n ℂ) (hf : Integrable f μ) (i : m) (j : n) :
    (∫ x, f x ∂μ) i j = ∫ x, f x i j ∂μ := by
  let L : Matrix m n ℂ →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) j).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : m => (n → ℂ)) i)
  have := L.integral_comp_comm hf
  exact this.symm


lemma X7L7_int_conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {m : Type*} [Fintype m]
    (A B : Matrix m m ℂ) (f : X → Matrix m m ℂ) (hf : Integrable f μ) :
    ∫ x, A * f x * B ∂μ = A * (∫ x, f x ∂μ) * B := by
  let L0 : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ :=
    { toFun := fun X => A * X * B
      map_add' := fun X Y => by simp [mul_add, add_mul]
      map_smul' := fun c X => by simp [Matrix.mul_smul, Matrix.smul_mul] }
  let L : Matrix m m ℂ →L[ℂ] Matrix m m ℂ := LinearMap.toContinuousLinearMap L0
  exact L.integral_comp_comm hf

lemma X7L7_int_trace {X : Type*} [MeasurableSpace X] {μ : Measure X} {m : Type*} [Fintype m]
    (f : X → Matrix m m ℂ) (hf : Integrable f μ) :
    ∫ x, (f x).trace ∂μ = (∫ x, f x ∂μ).trace := by
  let L : Matrix m m ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap m ℂ ℂ)
  exact L.integral_comp_comm hf

def MM {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ∫ U, ff S U ∂(QAlgorithms.Schur.unitaryHaar d)

lemma X7L7_MM_comm {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (V : G d) :
    MM S * KK (V : Matrix (Fin d) (Fin d) ℂ) = KK (V : Matrix (Fin d) (Fin d) ℂ) * MM S := by
  have hinv : (KK (V : Matrix (Fin d) (Fin d) ℂ))ᴴ * MM S * KK (V : Matrix (Fin d) (Fin d) ℂ) = MM S := by
    unfold MM
    rw [← X7L7_int_conj _ _ _ (X7L7_ff_int S)]
    have : ∀ U : G d, (KK (V : Matrix (Fin d) (Fin d) ℂ))ᴴ * ff S U * KK (V : Matrix (Fin d) (Fin d) ℂ)
        = ff S (U * V) := by
      intro U
      simp only [ff, Matrix.UnitaryGroup.mul_apply, X7L7_KK_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    simp_rw [this]
    exact X7L7_intRight d (ff S) V
  have hu := (X7L7_KK_unit V).2
  calc MM S * KK (V : Matrix (Fin d) (Fin d) ℂ)
      = (KK (V : Matrix (Fin d) (Fin d) ℂ) * (KK (V : Matrix (Fin d) (Fin d) ℂ))ᴴ) * MM S *
          KK (V : Matrix (Fin d) (Fin d) ℂ) := by rw [hu, Matrix.one_mul]
    _ = KK (V : Matrix (Fin d) (Fin d) ℂ) * ((KK (V : Matrix (Fin d) (Fin d) ℂ))ᴴ * MM S *
          KK (V : Matrix (Fin d) (Fin d) ℂ)) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hinv]

lemma X7L7_swap_KK {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : swap (Fin d) * KK U = KK U * swap (Fin d) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.mul_apply, swap, KK, Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]

lemma X7L7_tr_MM {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : (MM S).trace = S.trace := by
  unfold MM
  rw [← X7L7_int_trace _ (X7L7_ff_int S)]
  have : ∀ U : G d, (ff S U).trace = S.trace := by
    intro U
    simp only [ff]
    rw [Matrix.trace_mul_cycle, (X7L7_KK_unit U).2, Matrix.one_mul]
  simp [this]

lemma X7L7_tr_MMF {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (MM S * swap (Fin d)).trace = (S * swap (Fin d)).trace := by
  have h1 : MM S * swap (Fin d) = ∫ U, 1 * ff S U * swap (Fin d) ∂(QAlgorithms.Schur.unitaryHaar d) := by
    rw [X7L7_int_conj _ _ _ (X7L7_ff_int S), Matrix.one_mul]; rfl
  rw [h1, ← X7L7_int_trace]
  · have : ∀ U : G d, (1 * ff S U * swap (Fin d)).trace = (S * swap (Fin d)).trace := by
      intro U
      simp only [ff, Matrix.one_mul]
      have e : (KK (U : Matrix (Fin d) (Fin d) ℂ))ᴴ * S * KK (U : Matrix (Fin d) (Fin d) ℂ) * swap (Fin d)
          = (KK (U : Matrix (Fin d) (Fin d) ℂ))ᴴ * (S * swap (Fin d) * KK (U : Matrix (Fin d) (Fin d) ℂ)) := by
        rw [Matrix.mul_assoc _ (KK _), ← X7L7_swap_KK]; simp only [Matrix.mul_assoc]
      rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, (X7L7_KK_unit U).2, Matrix.mul_one]
    simp_rw [this]
    simp
  · exact (((continuous_const.matrix_mul (X7L7_ff_cont S)).matrix_mul continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

@[simp] lemma X7L7_and_symm {α : Type*} (a b : α) : (a = b ∧ b = a) ↔ a = b :=
  ⟨fun h => h.1, fun h => ⟨h, h.symm⟩⟩

lemma X7L7_trace_form {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (x y : ℂ)
    (h : ∀ i j k l : Fin d, M (i, j) (k, l) = (if i = k ∧ j = l then x else 0) + (if i = l ∧ j = k then y else 0)) :
    M.trace = (d : ℂ)^2 * x + d * y ∧ (M * swap (Fin d)).trace = d * x + (d : ℂ)^2 * y := by
  constructor
  · simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, h]
    simp [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
    ring
  · simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, h, swap]
    simp [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and, add_mul]
    ring

end X7L7


open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

noncomputable section
namespace X7L7

attribute [local instance] Classical.propDecidable Classical.decEq

def Sh (s b : ℕ) : Matrix ((Fin s × Fin b) × (Fin s × Fin b)) ((Fin s × Fin b) × (Fin s × Fin b)) ℂ :=
  fun p q => if p.1 = (q.1.1, q.2.2) ∧ p.2 = (q.2.1, q.1.2) then 1 else 0

def SW {s b c : ℕ} (W : Matrix (Fin s × Fin b) (Fin c) ℂ) : Matrix (Fin c × Fin c) (Fin c × Fin c) ℂ :=
  (Matrix.kronecker W W)ᴴ * Sh s b * Matrix.kronecker W W

lemma X7L7_dim {s b c : ℕ} (W : Matrix (Fin s × Fin b) (Fin c) ℂ)
    (hW : Wᴴ * W = 1 ∧ W * Wᴴ = 1) : c = s * b := by
  have h := congrArg Matrix.trace hW.1
  rw [Matrix.trace_mul_comm, hW.2, Matrix.trace_one, Matrix.trace_one] at h
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  exact_mod_cast h.symm

lemma X7L7_kk_unit {s b c : ℕ} (W : Matrix (Fin s × Fin b) (Fin c) ℂ)
    (hW : Wᴴ * W = 1 ∧ W * Wᴴ = 1) :
    Matrix.kronecker W W * (Matrix.kronecker W W)ᴴ = 1 := by
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hW.2]
  simp

lemma X7L7_tr_Sh (s b : ℕ) : (Sh s b).trace = (s : ℂ)^2 * b := by
  simp only [Matrix.trace, Matrix.diag, Sh, Fintype.sum_prod_type, Prod.mk.injEq]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and]
  ring

lemma X7L7_trF {X : Type*} [Fintype X] [DecidableEq X] (M : Matrix (X × X) (X × X) ℂ) :
    (M * swap X).trace = ∑ i, ∑ j, M (i, j) (j, i) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, swap, Fintype.sum_prod_type, mul_ite, mul_one,
    mul_zero, ite_and]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma X7L7_tr_ShF (s b : ℕ) : (Sh s b * swap (Fin s × Fin b)).trace = (s : ℂ) * b^2 := by
  rw [X7L7_trF]
  simp only [Sh, Fintype.sum_prod_type, Prod.mk.injEq]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and]
  try ring
  try simp

lemma X7L7_swap_kk {s b c : ℕ} (W : Matrix (Fin s × Fin b) (Fin c) ℂ) :
    Matrix.kronecker W W * swap (Fin c) = swap (Fin s × Fin b) * Matrix.kronecker W W := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.mul_apply, swap, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [Fintype.sum_eq_single (l, k), Fintype.sum_eq_single (j, i)]
  · simp [mul_comm]
  · rintro ⟨p, q⟩ h
    have : ¬ (i = q ∧ j = p) := by
      rintro ⟨rfl, rfl⟩; exact h rfl
    simp [this]
  · rintro ⟨p, q⟩ h
    have : ¬ (p = l ∧ q = k) := by
      rintro ⟨rfl, rfl⟩; exact h rfl
    simp [this]

lemma X7L7_tr_SW {s b c : ℕ} (W : Matrix (Fin s × Fin b) (Fin c) ℂ)
    (hW : Wᴴ * W = 1 ∧ W * Wᴴ = 1) : (SW W).trace = (s : ℂ)^2 * b := by
  rw [SW, Matrix.trace_mul_cycle, X7L7_kk_unit W hW, Matrix.one_mul, X7L7_tr_Sh]

lemma X7L7_tr_SWF {s b c : ℕ} (W : Matrix (Fin s × Fin b) (Fin c) ℂ)
    (hW : Wᴴ * W = 1 ∧ W * Wᴴ = 1) : (SW W * swap (Fin c)).trace = (s : ℂ) * b^2 := by
  have e : SW W * swap (Fin c) = (Matrix.kronecker W W)ᴴ * (Sh s b * swap (Fin s × Fin b) * Matrix.kronecker W W) := by
    rw [SW, Matrix.mul_assoc, X7L7_swap_kk]; simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, X7L7_kk_unit W hW, Matrix.mul_one, X7L7_tr_ShF]

lemma X7L7_twirl {s b c : ℕ} (hs : 0 < s) (hb : 0 < b) (W : Matrix (Fin s × Fin b) (Fin c) ℂ)
    (hW : Wᴴ * W = 1 ∧ W * Wᴴ = 1) :
    ∃ x y : ℝ, (∀ i j k l : Fin c, MM (SW W) (i, j) (k, l) =
      (if i = k ∧ j = l then (x : ℂ) else 0) + (if i = l ∧ j = k then (y : ℂ) else 0)) ∧
      x ≤ 1 / b ∧ y ≤ 1 / s := by
  have hc := X7L7_dim W hW
  have t1 := X7L7_tr_MM (SW W)
  have t2 := X7L7_tr_MMF (SW W)
  rw [X7L7_tr_SW W hW] at t1
  rw [X7L7_tr_SWF W hW] at t2
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  rcases Nat.lt_or_ge c 2 with hlt | hd2
  · have hc1 : c = 1 := by have := Nat.mul_pos hs hb; omega
    have hs1 : s = 1 := by rw [hc1] at hc; exact Nat.eq_one_of_mul_eq_one_right hc.symm
    have hb1 : b = 1 := by rw [hc1] at hc; exact Nat.eq_one_of_mul_eq_one_left hc.symm
    subst hc1 hs1 hb1
    refine ⟨1, 0, fun i j k l => ?_, by norm_num, by norm_num⟩
    have hi : ∀ q : Fin 1, q = 0 := fun q => Subsingleton.elim _ _
    rw [hi i, hi j, hi k, hi l]
    have : (MM (SW W)).trace = MM (SW W) (0, 0) (0, 0) := by
      simp [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
    rw [← this, t1]; simp
  · obtain ⟨x, y, hxy⟩ := X7L7_comm hd2 _ (X7L7_MM_comm (SW W))
    obtain ⟨u1, u2⟩ := X7L7_trace_form _ x y hxy
    rw [u1] at t1; rw [u2] at t2
    subst hc
    push_cast at t1 t2
    set xr : ℝ := (b:ℝ)*((s:ℝ)^2-1)/(((s:ℝ)*b)^2-1) with hxr
    set yr : ℝ := (s:ℝ)*((b:ℝ)^2-1)/(((s:ℝ)*b)^2-1) with hyr
    have hAB : (2 : ℝ) ≤ (s : ℝ) * b := by exact_mod_cast hd2
    have hD : (0:ℝ) < ((s:ℝ)*b)^2 - 1 := by nlinarith
    have hc0 : ((s : ℂ) * b) ≠ 0 := by
      intro h
      have : ((s : ℝ) * b : ℝ) = 0 := by exact_mod_cast h
      linarith
    have hc3 : ((s : ℂ) * b)^2 - 1 ≠ 0 := by
      intro h
      have : (((s : ℝ) * b)^2 - 1 : ℝ) = 0 := by exact_mod_cast h
      linarith
    have hx : x = (xr : ℂ) := by
      rw [hxr]; push_cast
      rw [eq_div_iff hc3]
      apply mul_left_cancel₀ hc0
      linear_combination ((s : ℂ) * b) * t1 - t2
    have hy : y = (yr : ℂ) := by
      rw [hyr]; push_cast
      rw [eq_div_iff hc3]
      apply mul_left_cancel₀ hc0
      linear_combination ((s : ℂ) * b) * t2 - t1
    refine ⟨xr, yr, fun i j k l => by rw [hxy, hx, hy], ?_, ?_⟩
    · rw [hxr, div_le_div_iff₀ hD (by linarith)]; nlinarith
    · rw [hyr, div_le_div_iff₀ hD (by linarith)]; nlinarith

end X7L7


open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

noncomputable section
namespace X7L7

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P38

lemma X7L7_tau_apply {m c e : Type*} [Fintype m] [Fintype c] [Fintype e] [DecidableEq e]
    (V : Matrix m c ℂ) (φ : Matrix (c × e) (c × e) ℂ) (x y : m) (ε ε' : e) :
    (Matrix.kronecker V (1 : Matrix e e ℂ) * φ * (Matrix.kronecker V (1 : Matrix e e ℂ))ᴴ) (x, ε) (y, ε') =
      ∑ i, ∑ j, V x i * φ (i, ε) (j, ε') * conj (V y j) := by
  simp only [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.one_apply, RCLike.star_def]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_mul]
  simp only [apply_ite (starRingEnd ℂ), map_zero, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [Finset.sum_comm]

lemma X7L7_rho_apply {c s b e : ℕ} (W : Matrix (Fin s × Fin b) (Fin c) ℂ)
    (φ : Matrix (Fin c × Fin e) (Fin c × Fin e) ℂ) (U : Matrix.unitaryGroup (Fin c) ℂ)
    (β β' : Fin b) (ε ε' : Fin e) :
    decouplingMarginal W φ U (β, ε) (β', ε') =
      ∑ a, ∑ i, ∑ j, (W * (U : Matrix (Fin c) (Fin c) ℂ)) (a, β) i * φ (i, ε) (j, ε') *
        conj ((W * (U : Matrix (Fin c) (Fin c) ℂ)) (a, β') j) := by
  unfold decouplingMarginal
  dsimp only
  refine Finset.sum_congr rfl fun a _ => ?_
  exact X7L7_tau_apply _ φ _ _ ε ε'

def Qv {s b c : ℕ} (V : Matrix (Fin s × Fin b) (Fin c) ℂ) (j l i k : Fin c) : ℂ :=
  ∑ a, ∑ β, ∑ a', ∑ β', conj (V (a, β') j) * conj (V (a', β) l) * V (a, β) i * V (a', β') k

lemma X7L7_ffV_apply {s b c : ℕ} (V : Matrix (Fin s × Fin b) (Fin c) ℂ) (j l i k : Fin c) :
    ((Matrix.kronecker V V)ᴴ * Sh s b * Matrix.kronecker V V) (j, l) (i, k) = Qv V j l i k := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Sh, Qv, RCLike.star_def, mul_ite, mul_one, mul_zero, star_mul']
  have key : ∀ q : (Fin s × Fin b) × (Fin s × Fin b),
      (∑ p : (Fin s × Fin b) × (Fin s × Fin b), if p.1 = (q.1.1, q.2.2) ∧ p.2 = (q.2.1, q.1.2) then
        (starRingEnd ℂ) (V p.1 j) * (starRingEnd ℂ) (V p.2 l) else 0) =
      (starRingEnd ℂ) (V (q.1.1, q.2.2) j) * (starRingEnd ℂ) (V (q.2.1, q.1.2) l) := by
    intro q
    rw [Fintype.sum_eq_single ((q.1.1, q.2.2), (q.2.1, q.1.2))]
    · simp
    · intro p hp
      rw [if_neg]
      contrapose! hp
      exact Prod.ext hp.1 hp.2
  simp only [key, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun β' _ => ?_
  ring

lemma X7L7_tr_sq {c s b e : ℕ} (W : Matrix (Fin s × Fin b) (Fin c) ℂ)
    (φ : Matrix (Fin c × Fin e) (Fin c × Fin e) ℂ) (U : Matrix.unitaryGroup (Fin c) ℂ) :
    (decouplingMarginal W φ U * decouplingMarginal W φ U).trace =
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ ε, ∑ ε', φ (i, ε) (j, ε') * φ (k, ε') (l, ε) *
        Qv (W * (U : Matrix (Fin c) (Fin c) ℂ)) j l i k := by
  generalize hV : W * (U : Matrix (Fin c) (Fin c) ℂ) = V
  have hρ : ∀ β β' ε ε', decouplingMarginal W φ U (β, ε) (β', ε') =
      ∑ a, ∑ i, ∑ j, V (a, β) i * φ (i, ε) (j, ε') * conj (V (a, β') j) := by
    intro β β' ε ε'; rw [X7L7_rho_apply, hV]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, hρ, Qv]
  simp only [Finset.mul_sum, Finset.sum_mul]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun ⟨β, ε, β', ε', a', k, l, a, i, j⟩ => ⟨i, j, k, l, ε, ε', a, β, a', β'⟩
      invFun := fun ⟨i, j, k, l, ε, ε', a, β, a', β'⟩ => ⟨β, ε, β', ε', a', k, l, a, i, j⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ (fun x => ?_)
  obtain ⟨β, ε, β', ε', a', k, l, a, i, j⟩ := x
  simp only [Equiv.coe_fn_mk]
  ring

end X7L7


open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

noncomputable section
namespace X7L7

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P38

lemma X7L7_Qv_eq {s b c : ℕ} (W : Matrix (Fin s × Fin b) (Fin c) ℂ) (U : G c) (j l i k : Fin c) :
    Qv (W * (U : Matrix (Fin c) (Fin c) ℂ)) j l i k = ff (SW W) U (j, l) (i, k) := by
  rw [← X7L7_ffV_apply]
  have hm : (Matrix.kronecker (W * (U : Matrix (Fin c) (Fin c) ℂ)) (W * (U : Matrix (Fin c) (Fin c) ℂ)))ᴴ *
      Sh s b * Matrix.kronecker (W * (U : Matrix (Fin c) (Fin c) ℂ)) (W * (U : Matrix (Fin c) (Fin c) ℂ)) =
      ff (SW W) U := by
    simp only [ff, SW, KK, Matrix.kronecker]
    rw [Matrix.mul_kronecker_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [hm]

lemma X7L7_trsq_ff {c s b e : ℕ} (W : Matrix (Fin s × Fin b) (Fin c) ℂ)
    (φ : Matrix (Fin c × Fin e) (Fin c × Fin e) ℂ) (U : G c) :
    (decouplingMarginal W φ U * decouplingMarginal W φ U).trace =
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ ε, ∑ ε', φ (i, ε) (j, ε') * φ (k, ε') (l, ε) * ff (SW W) U (j, l) (i, k) := by
  rw [X7L7_tr_sq]
  simp only [X7L7_Qv_eq]

lemma X7L7_trsq_cont {c s b e : ℕ} (W : Matrix (Fin s × Fin b) (Fin c) ℂ)
    (φ : Matrix (Fin c × Fin e) (Fin c × Fin e) ℂ) :
    Continuous (fun U : G c => (decouplingMarginal W φ U * decouplingMarginal W φ U).trace.re) := by
  simp only [X7L7_trsq_ff]
  have hc : ∀ p q, Continuous (fun U : G c => ff (SW W) U p q) :=
    fun p q => (X7L7_ff_cont _).matrix_elem p q
  fun_prop

lemma X7L7_int_trsq {c s b e : ℕ} (W : Matrix (Fin s × Fin b) (Fin c) ℂ)
    (φ : Matrix (Fin c × Fin e) (Fin c × Fin e) ℂ) (x y : ℝ)
    (hxy : ∀ i j k l : Fin c, MM (SW W) (i, j) (k, l) =
      (if i = k ∧ j = l then (x : ℂ) else 0) + (if i = l ∧ j = k then (y : ℂ) else 0)) :
    ∫ U : G c, (decouplingMarginal W φ U * decouplingMarginal W φ U).trace.re ∂(Schur.unitaryHaar c) =
      x * (traceLeft φ * traceLeft φ).trace.re + y * (φ * φ).trace.re := by
  have hI : ∀ f : G c → ℂ, Continuous f → Integrable f (Schur.unitaryHaar c) :=
    fun f hf => hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hc : ∀ p q, Continuous (fun U : G c => ff (SW W) U p q) :=
    fun p q => (X7L7_ff_cont _).matrix_elem p q
  have hv : ∀ p q, ∫ U, ff (SW W) U p q ∂(Schur.unitaryHaar c) = MM (SW W) p q := by
    intro p q
    rw [MM, X7L7_entry' _ (X7L7_ff_int _)]
  simp only [X7L7_trsq_ff]
  have hre := integral_re (𝕜 := ℂ) (hI (fun U : G c =>
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ ε, ∑ ε', φ (i, ε) (j, ε') * φ (k, ε') (l, ε) * ff (SW W) U (j, l) (i, k))
      (by fun_prop))
  simp only [RCLike.re_to_complex] at hre
  rw [hre]
  have hsum : ∫ U : G c, (∑ i, ∑ j, ∑ k, ∑ l, ∑ ε, ∑ ε', φ (i, ε) (j, ε') * φ (k, ε') (l, ε) *
      ff (SW W) U (j, l) (i, k)) ∂(Schur.unitaryHaar c) =
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ ε, ∑ ε', φ (i, ε) (j, ε') * φ (k, ε') (l, ε) * MM (SW W) (j, l) (i, k) := by
    rw [integral_finsetSum _ (fun _ _ => hI _ (by fun_prop))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun _ _ => hI _ (by fun_prop))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ (fun _ _ => hI _ (by fun_prop))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ (fun _ _ => hI _ (by fun_prop))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_finsetSum _ (fun _ _ => hI _ (by fun_prop))]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [integral_finsetSum _ (fun _ _ => hI _ (by fun_prop))]
    refine Finset.sum_congr rfl fun ε' _ => ?_
    rw [integral_const_mul, hv]
  rw [hsum]
  simp only [hxy, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, ite_and]
  have h1 : ∑ i : Fin c, ∑ j : Fin c, ∑ k : Fin c, ∑ l : Fin c, ∑ ε : Fin e, ∑ ε' : Fin e,
      (if j = i then (if l = k then φ (i, ε) (j, ε') * φ (k, ε') (l, ε) * (x : ℂ) else 0) else 0) =
      (x : ℂ) * (traceLeft φ * traceLeft φ).trace := by
    calc _ = ∑ i : Fin c, ∑ k : Fin c, ∑ ε : Fin e, ∑ ε' : Fin e,
          φ (i, ε) (i, ε') * φ (k, ε') (k, ε) * (x : ℂ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Fintype.sum_eq_single i (fun j hj => by simp [hj])]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Fintype.sum_eq_single k (fun l hl => by simp [hl])]
          simp
      _ = _ := by
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, traceLeft, Matrix.of_apply, Finset.sum_mul,
            Finset.mul_sum]
          simp only [← Fintype.sum_prod_type']
          refine Fintype.sum_equiv
            { toFun := fun ⟨i, k, ε, ε'⟩ => ⟨ε, ε', k, i⟩
              invFun := fun ⟨ε, ε', k, i⟩ => ⟨i, k, ε, ε'⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl } _ _ (fun z => ?_)
          obtain ⟨i, k, ε, ε'⟩ := z
          simp only [Equiv.coe_fn_mk]
          ring
  have h2 : ∑ i : Fin c, ∑ j : Fin c, ∑ k : Fin c, ∑ l : Fin c, ∑ ε : Fin e, ∑ ε' : Fin e,
      (if j = k then (if l = i then φ (i, ε) (j, ε') * φ (k, ε') (l, ε) * (y : ℂ) else 0) else 0) =
      (y : ℂ) * (φ * φ).trace := by
    calc _ = ∑ i : Fin c, ∑ j : Fin c, ∑ ε : Fin e, ∑ ε' : Fin e,
          φ (i, ε) (j, ε') * φ (j, ε') (i, ε) * (y : ℂ) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [Fintype.sum_eq_single j (fun k hk => by simp [Ne.symm hk])]
          rw [Fintype.sum_eq_single i (fun l hl => by simp [hl])]
          simp
      _ = _ := by
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_mul,
            Finset.mul_sum]
          simp only [← Fintype.sum_prod_type']
          refine Fintype.sum_equiv
            { toFun := fun ⟨i, j, ε, ε'⟩ => ⟨i, ε, j, ε'⟩
              invFun := fun ⟨i, ε, j, ε'⟩ => ⟨i, j, ε, ε'⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl } _ _ (fun z => ?_)
          obtain ⟨i, j, ε, ε'⟩ := z
          simp only [Equiv.coe_fn_mk]
          ring
  rw [h1, h2]
  simp only [Complex.add_re, Complex.re_ofReal_mul]

end X7L7


open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

noncomputable section
namespace X7L7

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P38

lemma X7L7_frob_sq {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℂ) :
    frobNorm X ^ 2 = (X * Xᴴ).trace.re := by
  unfold frobNorm
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  norm_cast

lemma X7L7_trL {c s b e : ℕ} (W : Matrix (Fin s × Fin b) (Fin c) ℂ) (hW : Wᴴ * W = 1)
    (φ : Matrix (Fin c × Fin e) (Fin c × Fin e) ℂ) (U : G c) :
    traceLeft (decouplingMarginal W φ U) = traceLeft φ := by
  have hV : (W * (U : Matrix (Fin c) (Fin c) ℂ))ᴴ * (W * (U : Matrix (Fin c) (Fin c) ℂ)) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ, hW, Matrix.one_mul]
    exact Matrix.UnitaryGroup.star_mul_self U
  ext ε ε'
  simp only [traceLeft, Matrix.of_apply, X7L7_rho_apply]
  generalize W * (U : Matrix (Fin c) (Fin c) ℂ) = V at hV
  have h1 : ∀ i j, ∑ a, ∑ β, conj (V (a, β) j) * V (a, β) i = if j = i then 1 else 0 := by
    intro i j
    have := congrFun (congrFun hV j) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, RCLike.star_def,
      Matrix.one_apply] at this
    exact this
  calc ∑ β : Fin b, ∑ a : Fin s, ∑ i : Fin c, ∑ j : Fin c, V (a, β) i * φ (i, ε) (j, ε') * conj (V (a, β) j)
      = ∑ i : Fin c, ∑ j : Fin c, φ (i, ε) (j, ε') * ∑ a : Fin s, ∑ β : Fin b, conj (V (a, β) j) * V (a, β) i := by
        simp only [Finset.mul_sum]
        simp only [← Fintype.sum_prod_type']
        refine Fintype.sum_equiv
          { toFun := fun ⟨β, a, i, j⟩ => ⟨i, j, a, β⟩
            invFun := fun ⟨i, j, a, β⟩ => ⟨β, a, i, j⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl } _ _ (fun z => ?_)
        obtain ⟨β, a, i, j⟩ := z
        simp only [Equiv.coe_fn_mk]
        ring
    _ = ∑ i, φ (i, ε) (i, ε') := by
        simp only [h1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma X7L7_rho_herm {c s b e : ℕ} (W : Matrix (Fin s × Fin b) (Fin c) ℂ)
    (φ : Matrix (Fin c × Fin e) (Fin c × Fin e) ℂ) (hφ : φᴴ = φ) (U : G c) :
    (decouplingMarginal W φ U)ᴴ = decouplingMarginal W φ U := by
  ext ⟨β, ε⟩ ⟨β', ε'⟩
  rw [Matrix.conjTranspose_apply, X7L7_rho_apply, X7L7_rho_apply]
  generalize W * (U : Matrix (Fin c) (Fin c) ℂ) = V
  have hφ' : ∀ p q, star (φ p q) = φ q p := fun p q => by
    rw [← Matrix.conjTranspose_apply, hφ]
  simp only [star_sum, star_mul', RCLike.star_def, Complex.conj_conj]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := hφ' (j, ε') (i, ε)
  rw [RCLike.star_def] at this
  rw [this]
  ring

lemma X7L7_trK {b e : ℕ} (ρ : Matrix (Fin b × Fin e) (Fin b × Fin e) ℂ) (φE : Matrix (Fin e) (Fin e) ℂ)
    (hL : traceLeft ρ = φE) :
    (ρ * Matrix.kronecker (QAlgorithms.Papers.Independent.Information100.P08.maximallyMixed b) φE).trace =
      (b : ℂ)⁻¹ * (φE * φE).trace := by
  rw [← hL]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, QAlgorithms.Papers.Independent.Information100.P08.maximallyMixed,
    Matrix.smul_apply, Matrix.one_apply, traceLeft, Matrix.of_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.mul_sum, Finset.sum_mul]
  have h : ∀ (β : Fin b) (ε : Fin e), (∑ β' : Fin b, ∑ ε' : Fin e, ∑ β'' : Fin b,
      if β' = β then ρ (β, ε) (β', ε') * ((b : ℂ)⁻¹ * ρ (β'', ε') (β'', ε)) else 0) =
      ∑ ε' : Fin e, ∑ β'' : Fin b, ρ (β, ε) (β, ε') * ((b : ℂ)⁻¹ * ρ (β'', ε') (β'', ε)) := by
    intro β ε
    rw [Fintype.sum_eq_single β (fun β' hβ' => by simp [hβ'])]
    simp
  simp only [h]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun ⟨β, ε, ε', β''⟩ => ⟨ε, ε', β'', β⟩
      invFun := fun ⟨ε, ε', β'', β⟩ => ⟨β, ε, ε', β''⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ (fun z => ?_)
  obtain ⟨β, ε, ε', β''⟩ := z
  simp only [Equiv.coe_fn_mk]
  ring

lemma X7L7_frob_X {b e : ℕ} (hb : 0 < b) (ρ : Matrix (Fin b × Fin e) (Fin b × Fin e) ℂ)
    (φE : Matrix (Fin e) (Fin e) ℂ) (hρ : ρᴴ = ρ) (hE : φEᴴ = φE) (hL : traceLeft ρ = φE) :
    frobNorm (ρ - Matrix.kronecker (QAlgorithms.Papers.Independent.Information100.P08.maximallyMixed b) φE) ^ 2 =
      (ρ * ρ).trace.re - (φE * φE).trace.re / b := by
  set K := Matrix.kronecker (QAlgorithms.Papers.Independent.Information100.P08.maximallyMixed b) φE with hK
  have hKh : Kᴴ = K := by
    rw [hK]; simp only [Matrix.kronecker]; rw [Matrix.conjTranspose_kronecker, hE]
    congr 1
    simp [QAlgorithms.Papers.Independent.Information100.P08.maximallyMixed, Matrix.conjTranspose_smul]
  have hKK : (K * K).trace = (b : ℂ)⁻¹ * (φE * φE).trace := by
    rw [hK]; simp only [Matrix.kronecker]; rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
    simp only [QAlgorithms.Papers.Independent.Information100.P08.maximallyMixed, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, smul_smul, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
      smul_eq_mul]
    have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    field_simp
  have hρK := X7L7_trK ρ φE hL
  rw [← hK] at hρK
  have hKρ : (K * ρ).trace = (b : ℂ)⁻¹ * (φE * φE).trace := by rw [Matrix.trace_mul_comm, hρK]
  rw [X7L7_frob_sq, Matrix.conjTranspose_sub, hρ, hKh]
  have e : (ρ - K) * (ρ - K) = ρ * ρ - ρ * K - K * ρ + K * K := by
    simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
  rw [e, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, hρK, hKρ, hKK]
  simp only [Complex.add_re, Complex.sub_re]
  have hre : ((b : ℂ)⁻¹ * (φE * φE).trace).re = (φE * φE).trace.re / b := by
    rw [show (b : ℂ)⁻¹ = ((b : ℝ)⁻¹ : ℝ) by push_cast; rfl, Complex.re_ofReal_mul]
    ring
  rw [hre]
  ring

end X7L7


open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ComplexOrder

noncomputable section
namespace X7L7

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P38

lemma X7L7_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma X7L7_tn_rank {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    traceNorm M ^ 2 ≤ M.rank * (Mᴴ * M).trace.re := by
  have hH : (Mᴴ * M).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  have hp := Matrix.posSemidef_conjTranspose_mul_self M
  unfold traceNorm
  rw [X7L7_cfc_trace hH, hH.trace_eq_sum_eigenvalues]
  simp only [Complex.re_sum, Complex.ofReal_re, RCLike.ofReal_re]
  set T := Finset.univ.filter (fun i => hH.eigenvalues i ≠ 0) with hT
  have hrank : M.rank = T.card := by
    rw [← Matrix.rank_conjTranspose_mul_self, hH.rank_eq_card_non_zero_eigs, hT, Fintype.card_subtype]
  have e1 : ∑ i, Real.sqrt (hH.eigenvalues i) = ∑ i ∈ T, Real.sqrt (hH.eigenvalues i) := by
    rw [hT, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · push_neg at h; rw [h, Real.sqrt_zero]
  have e2 : ∑ i, hH.eigenvalues i = ∑ i ∈ T, hH.eigenvalues i := by
    rw [hT, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · push_neg at h; rw [h]
  rw [e1, hrank]
  have hS : ∑ i ∈ T, hH.eigenvalues i ≤ ∑ i, hH.eigenvalues i := le_of_eq e2.symm
  have := sq_sum_le_card_mul_sum_sq (s := T) (f := fun i => Real.sqrt (hH.eigenvalues i))
  refine this.trans (le_of_eq ?_)
  congr 1
  trans ∑ i ∈ T, hH.eigenvalues i
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.sq_sqrt (hp.eigenvalues_nonneg i)]
  · rw [← e2]
    exact Finset.sum_congr rfl (fun i _ => by simp)

end X7L7


open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ComplexOrder

noncomputable section
namespace X7L7

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P38

lemma X7L7_proj {e : ℕ} (b : ℕ) (φE : Matrix (Fin e) (Fin e) ℂ) (hH : φE.IsHermitian) :
    ∃ P : Matrix (Fin e) (Fin e) ℂ, Pᴴ = P ∧ P * P = P ∧ φE * P = φE ∧
      (Matrix.kronecker (1 : Matrix (Fin b) (Fin b) ℂ) P).rank ≤ b * φE.rank := by
  set U : Matrix (Fin e) (Fin e) ℂ := (hH.eigenvectorUnitary : Matrix (Fin e) (Fin e) ℂ) with hU
  have hU1 : star U * U = 1 := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hU2 : U * star U = 1 := Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  set d : Fin e → ℂ := fun i => if hH.eigenvalues i = 0 then 0 else 1 with hd
  have hspec : φE = U * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  refine ⟨U * Matrix.diagonal d * star U, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose,
      ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, star_star, Matrix.mul_assoc]
    have hs : star d = d := by
      funext i; simp only [hd, Pi.star_apply]; split_ifs <;> simp
    rw [hs]
  · have : U * Matrix.diagonal d * star U * (U * Matrix.diagonal d * star U) =
        U * (Matrix.diagonal d * (star U * U) * Matrix.diagonal d) * star U := by
      simp only [Matrix.mul_assoc]
    rw [this, hU1, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
    congr 3
    ext i
    simp only [hd]
    split_ifs <;> simp
  · refine Eq.trans ?_ hspec.symm
    calc φE * (U * Matrix.diagonal d * star U) =
        U * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U * (U * Matrix.diagonal d * star U) := by
          rw [← hspec]
      _ = _ := ?_
    have : U * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U * (U * Matrix.diagonal d * star U) =
        U * (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) * (star U * U) * Matrix.diagonal d) * star U := by
      simp only [Matrix.mul_assoc]
    rw [this, hU1, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
    congr 3
    ext i
    simp only [hd, Function.comp_apply]
    split_ifs with h
    · simp [h]
    · simp
  · have hk : Matrix.kronecker (1 : Matrix (Fin b) (Fin b) ℂ) (U * Matrix.diagonal d * star U) =
        Matrix.kronecker (1 : Matrix (Fin b) (Fin b) ℂ) U *
          Matrix.kronecker (1 : Matrix (Fin b) (Fin b) ℂ) (Matrix.diagonal d) *
          Matrix.kronecker (1 : Matrix (Fin b) (Fin b) ℂ) (star U) := by
      simp only [Matrix.kronecker]
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
      simp
    rw [hk]
    refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans ?_)
    have hdiag : Matrix.kronecker (1 : Matrix (Fin b) (Fin b) ℂ) (Matrix.diagonal d) =
        Matrix.diagonal (fun p : Fin b × Fin e => d p.2) := by
      rw [← Matrix.diagonal_one]
      simp only [Matrix.kronecker]
      rw [Matrix.diagonal_kronecker_diagonal]
      simp
    rw [hdiag, Matrix.rank_diagonal, hH.rank_eq_card_non_zero_eigs]
    have e1 : Fintype.card {p : Fin b × Fin e // d p.2 ≠ 0} =
        Fintype.card (Fin b × {i : Fin e // hH.eigenvalues i ≠ 0}) := by
      refine Fintype.card_congr
        { toFun := fun p => (p.1.1, ⟨p.1.2, fun h => p.2 (by simp only [hd]; rw [if_pos h])⟩)
          invFun := fun q => ⟨(q.1, q.2.1), by simp only [hd]; rw [if_neg q.2.2]; simp⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [e1, Fintype.card_prod, Fintype.card_fin]

end X7L7


open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ComplexOrder MatrixOrder

noncomputable section
namespace X7L7

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P38

lemma X7L7_kronQ_apply {α : Type*} [Fintype α] [DecidableEq α] {e : ℕ}
    (M : Matrix (α × Fin e) (α × Fin e) ℂ) (Q : Matrix (Fin e) (Fin e) ℂ) (x y : α) (ε ε' : Fin e) :
    (M * Matrix.kronecker (1 : Matrix α α ℂ) Q) (x, ε) (y, ε') = ∑ ε'', M (x, ε) (y, ε'') * Q ε'' ε' := by
  simp only [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [Fintype.sum_eq_single y (fun z hz => by simp [hz])]
  simp

lemma X7L7_trQ {c e : ℕ} (φ : Matrix (Fin c × Fin e) (Fin c × Fin e) ℂ) (Q : Matrix (Fin e) (Fin e) ℂ) :
    (φ * Matrix.kronecker (1 : Matrix (Fin c) (Fin c) ℂ) Q).trace = (traceLeft φ * Q).trace := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
  simp only [X7L7_kronQ_apply]
  simp only [Matrix.mul_apply, traceLeft, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_comm

lemma X7L7_kill {c e : ℕ} (φ : Matrix (Fin c × Fin e) (Fin c × Fin e) ℂ) (hφ : φ.PosSemidef)
    (Q : Matrix (Fin e) (Fin e) ℂ) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q) (h : traceLeft φ * Q = 0) :
    φ * Matrix.kronecker (1 : Matrix (Fin c) (Fin c) ℂ) Q = 0 := by
  set K := Matrix.kronecker (1 : Matrix (Fin c) (Fin c) ℂ) Q with hK
  have hKh : Kᴴ = K := by
    rw [hK]; simp only [Matrix.kronecker]; rw [Matrix.conjTranspose_kronecker, hQ, Matrix.conjTranspose_one]
  have hKK : K * K = K := by
    rw [hK]; simp only [Matrix.kronecker]; rw [← Matrix.mul_kronecker_mul, hQQ, Matrix.one_mul]
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hφ.nonneg
  rw [Matrix.star_eq_conjTranspose] at hB
  have h0 : ((B * K)ᴴ * (B * K)).trace = 0 := by
    rw [Matrix.conjTranspose_mul, hKh]
    have : K * Bᴴ * (B * K) = K * (Bᴴ * B * K) := by simp only [Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm, Matrix.mul_assoc, hKK, ← hB, hK, X7L7_trQ, h, Matrix.trace_zero]
  have hBK : B * K = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h0
  rw [hB, Matrix.mul_assoc, hBK, Matrix.mul_zero]

lemma X7L7_rhoQ {c s b e : ℕ} (W : Matrix (Fin s × Fin b) (Fin c) ℂ)
    (φ : Matrix (Fin c × Fin e) (Fin c × Fin e) ℂ) (U : G c) (Q : Matrix (Fin e) (Fin e) ℂ)
    (h : φ * Matrix.kronecker (1 : Matrix (Fin c) (Fin c) ℂ) Q = 0) :
    decouplingMarginal W φ U * Matrix.kronecker (1 : Matrix (Fin b) (Fin b) ℂ) Q = 0 := by
  have h' : ∀ i j ε ε', ∑ ε'', φ (i, ε) (j, ε'') * Q ε'' ε' = 0 := by
    intro i j ε ε'
    rw [← X7L7_kronQ_apply, h, Matrix.zero_apply]
  ext ⟨β, ε⟩ ⟨β', ε'⟩
  rw [X7L7_kronQ_apply, Matrix.zero_apply]
  simp only [X7L7_rho_apply]
  generalize W * (U : Matrix (Fin c) (Fin c) ℂ) = V
  calc ∑ ε'' : Fin e, (∑ a : Fin s, ∑ i : Fin c, ∑ j : Fin c, V (a, β) i * φ (i, ε) (j, ε'') *
        conj (V (a, β') j)) * Q ε'' ε'
      = ∑ a : Fin s, ∑ i : Fin c, ∑ j : Fin c, V (a, β) i * conj (V (a, β') j) *
          ∑ ε'' : Fin e, φ (i, ε) (j, ε'') * Q ε'' ε' := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        simp only [← Fintype.sum_prod_type']
        refine Fintype.sum_equiv
          { toFun := fun ⟨ε'', a, i, j⟩ => ⟨a, i, j, ε''⟩
            invFun := fun ⟨a, i, j, ε''⟩ => ⟨ε'', a, i, j⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl } _ _ (fun z => ?_)
        obtain ⟨ε'', a, i, j⟩ := z
        simp only [Equiv.coe_fn_mk]
        ring
    _ = 0 := by simp [h']

end X7L7


noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P38 X7L7 in
theorem solution
    (c s b e : ℕ) (hc : 0 < c) (hs : 0 < s) (hb : 0 < b) (he : 0 < e)
    (phi : Matrix (Fin c × Fin e) (Fin c × Fin e) ℂ)
    (hphi : IsDensityMatrix phi)
    (W : Matrix (Fin s × Fin b) (Fin c) ℂ)
    (hW : Wᴴ * W = 1 ∧ W * Wᴴ = 1) :
    (∫ U : Matrix.unitaryGroup (Fin c) ℂ,
      traceNorm (decouplingMarginal W phi U -
        Matrix.kronecker (QAlgorithms.Papers.Independent.Information100.P08.maximallyMixed b) (traceLeft phi)) ^ 2 ∂Schur.unitaryHaar c) ≤
      (c : ℝ) * (Matrix.rank (traceLeft phi) : ℝ) * frobNorm phi ^ 2 / (s : ℝ) ^ 2 := by
  set φE := traceLeft phi with hφEdef
  set π := QAlgorithms.Papers.Independent.Information100.P08.maximallyMixed b with hπ
  have hφh : phiᴴ = phi := hphi.1.1
  have hEh : φEᴴ = φE := by
    ext ε ε'
    simp only [hφEdef, traceLeft, Matrix.conjTranspose_apply, Matrix.of_apply, star_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Matrix.conjTranspose_apply, hφh]
  have hEH : φE.IsHermitian := hEh
  obtain ⟨P, hPh, hPP, hφP, hrankP⟩ := X7L7_proj b φE hEH
  set Q := 1 - P with hQ
  have hQh : Qᴴ = Q := by rw [hQ, Matrix.conjTranspose_sub, hPh, Matrix.conjTranspose_one]
  have hQQ : Q * Q = Q := by
    rw [hQ, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPP, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul]; abel
  have hφQ : φE * Q = 0 := by rw [hQ, Matrix.mul_sub, hφP, Matrix.mul_one, sub_self]
  have hkill := X7L7_kill phi hphi.1 Q hQh hQQ hφQ
  set r : ℕ := φE.rank with hr
  have hPQ : Matrix.kronecker (1 : Matrix (Fin b) (Fin b) ℂ) P =
      1 - Matrix.kronecker (1 : Matrix (Fin b) (Fin b) ℂ) Q := by
    have hsum : P + Q = 1 := by rw [hQ]; abel
    have : Matrix.kronecker (1 : Matrix (Fin b) (Fin b) ℂ) P + Matrix.kronecker (1 : Matrix (Fin b) (Fin b) ℂ) Q = 1 := by
      simp only [Matrix.kronecker]
      rw [← Matrix.kronecker_add, hsum, Matrix.one_kronecker_one]
    rw [← this]; abel
  -- rank bound
  have hrank : ∀ U : G c, (decouplingMarginal W phi U - Matrix.kronecker π φE).rank ≤ b * r := by
    intro U
    have h1 : (decouplingMarginal W phi U - Matrix.kronecker π φE) *
        Matrix.kronecker (1 : Matrix (Fin b) (Fin b) ℂ) P =
        decouplingMarginal W phi U - Matrix.kronecker π φE := by
      rw [Matrix.sub_mul]
      congr 1
      · rw [hPQ, Matrix.mul_sub, Matrix.mul_one, X7L7_rhoQ W phi U Q hkill, sub_zero]
      · simp only [Matrix.kronecker]
        rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, hφP]
    rw [← h1]
    exact (Matrix.rank_mul_le_right _ _).trans hrankP
  -- pointwise bound
  have hpt : ∀ U : G c, traceNorm (decouplingMarginal W phi U - Matrix.kronecker π φE) ^ 2 ≤
      ((b : ℝ) * r) * ((decouplingMarginal W phi U * decouplingMarginal W phi U).trace.re -
        (φE * φE).trace.re / b) := by
    intro U
    set X := decouplingMarginal W phi U - Matrix.kronecker π φE with hX
    have h1 := X7L7_tn_rank X
    have hf := X7L7_frob_X hb (decouplingMarginal W phi U) φE (X7L7_rho_herm W phi hφh U) hEh
      (X7L7_trL W hW.1 phi U)
    rw [← hπ, ← hX, X7L7_frob_sq, ← Matrix.trace_mul_comm] at hf
    rw [hf] at h1
    refine h1.trans ?_
    have h0 : 0 ≤ (decouplingMarginal W phi U * decouplingMarginal W phi U).trace.re - (φE * φE).trace.re / b := by
      rw [← hf]; rw [Matrix.trace_mul_comm, ← X7L7_frob_sq]; positivity
    have hr' : (X.rank : ℝ) ≤ (b : ℝ) * r := by exact_mod_cast hrank U
    exact mul_le_mul_of_nonneg_right hr' h0
  obtain ⟨x, y, hxy, hx, hy⟩ := X7L7_twirl hs hb W hW
  have hcont := X7L7_trsq_cont W phi
  have hgi : Integrable (fun U : G c => ((b : ℝ) * r) * ((decouplingMarginal W phi U *
      decouplingMarginal W phi U).trace.re - (φE * φE).trace.re / b)) (Schur.unitaryHaar c) :=
    ((continuous_const.mul (hcont.sub continuous_const))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun U => sq_nonneg _)) hgi
    (Filter.Eventually.of_forall hpt)).trans ?_
  have hgi2 : Integrable (fun U : G c => (decouplingMarginal W phi U *
      decouplingMarginal W phi U).trace.re) (Schur.unitaryHaar c) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_const_mul, integral_sub hgi2 (integrable_const _), integral_const,
    X7L7_int_trsq W phi x y hxy]
  simp only [probReal_univ, one_smul, smul_eq_mul, one_mul]
  have hA : 0 ≤ (φE * φE).trace.re := by
    have := X7L7_frob_sq φE; rw [hEh] at this; rw [← this]; positivity
  have hB : (phi * phi).trace.re = frobNorm phi ^ 2 := by
    rw [X7L7_frob_sq, hφh]
  have hcsb : (c : ℝ) = s * b := by exact_mod_cast X7L7_dim W hW
  rw [← hB, hcsb]
  have hB0 : 0 ≤ (phi * phi).trace.re := by rw [hB]; positivity
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hr0 : (0 : ℝ) ≤ (b : ℝ) * r := by positivity
  have k1 : x * (φE * φE).trace.re - (φE * φE).trace.re / b ≤ 0 := by
    have : x * (φE * φE).trace.re ≤ (1 / b) * (φE * φE).trace.re := mul_le_mul_of_nonneg_right hx hA
    rw [div_eq_mul_one_div _ (b : ℝ)] ; nlinarith
  have k2 : y * (phi * phi).trace.re ≤ (1 / s) * (phi * phi).trace.re := mul_le_mul_of_nonneg_right hy hB0
  calc (b : ℝ) * r * (x * (φE * φE).trace.re + y * (phi * phi).trace.re - (φE * φE).trace.re / b)
      ≤ (b : ℝ) * r * ((1 / s) * (phi * phi).trace.re) := by
        apply mul_le_mul_of_nonneg_left _ hr0; linarith
    _ = (s : ℝ) * b * r * (phi * phi).trace.re / (s : ℝ) ^ 2 := by
        field_simp

