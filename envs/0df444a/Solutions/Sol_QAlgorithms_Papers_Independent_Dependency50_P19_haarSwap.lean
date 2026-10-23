-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P19.haarSwap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:07:45.243703+00:00
-- url     : https://prove2.me/submissions/ccbcfb15-ef87-40fa-b864-8a669dd64ea8

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

noncomputable section
namespace X7N

attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable instance X7N_cen {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) := SeminormedAddGroup.toContinuousENorm

instance X7N_haar (d : ℕ) : (QAlgorithms.Schur.unitaryHaar d).IsHaarMeasure := by
  unfold QAlgorithms.Schur.unitaryHaar; infer_instance

abbrev G (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ

def KK {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.kronecker U U

def ff {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (U : G d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (KK (U : Matrix (Fin d) (Fin d) ℂ))ᴴ * S * KK (U : Matrix (Fin d) (Fin d) ℂ)

lemma X7N_KK_cont (d : ℕ) : Continuous (fun U : G d => KK (U : Matrix (Fin d) (Fin d) ℂ)) := by
  have hU : Continuous (fun U : G d => (U : Matrix (Fin d) (Fin d) ℂ)) := continuous_subtype_val
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [KK]
  exact (hU.matrix_elem i.1 j.1).mul (hU.matrix_elem i.2 j.2)

lemma X7N_ff_cont {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Continuous (ff S) := by
  unfold ff
  exact ((X7N_KK_cont d).matrix_conjTranspose.matrix_mul continuous_const).matrix_mul (X7N_KK_cont d)

lemma X7N_ff_int {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Integrable (ff S) (QAlgorithms.Schur.unitaryHaar d) :=
  (X7N_ff_cont S).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma X7N_KK_mul {d : ℕ} (U V : Matrix (Fin d) (Fin d) ℂ) : KK (U * V) = KK U * KK V := by
  unfold KK; simp only [Matrix.kronecker]; rw [Matrix.mul_kronecker_mul]

lemma X7N_KK_unit {d : ℕ} (U : G d) : (KK (U : Matrix (Fin d) (Fin d) ℂ))ᴴ * KK (U : Matrix (Fin d) (Fin d) ℂ) = 1 ∧
    KK (U : Matrix (Fin d) (Fin d) ℂ) * (KK (U : Matrix (Fin d) (Fin d) ℂ))ᴴ = 1 := by
  have h1 : (U : Matrix (Fin d) (Fin d) ℂ)ᴴ * U = 1 := Matrix.UnitaryGroup.star_mul_self U
  have h2 : (U : Matrix (Fin d) (Fin d) ℂ) * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp U.2
    rwa [Matrix.star_eq_conjTranspose] at this
  unfold KK
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, h1, h2]
  simp


lemma X7N_phase_aux {X : Type*} [DecidableEq X] (a b c e : X)
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

lemma X7N_diag_unit {d : ℕ} (s : Fin d) :
    Matrix.diagonal (fun t : Fin d => if t = s then Complex.I else 1) ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1; funext t
  by_cases h : t = s <;> simp [h]

lemma X7N_phase {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : ∀ V : G d, M * KK (V : Matrix (Fin d) (Fin d) ℂ) = KK (V : Matrix (Fin d) (Fin d) ℂ) * M)
    (i j k l : Fin d) (hne : M (i, j) (k, l) ≠ 0) : (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  apply X7N_phase_aux
  intro s
  have := congrFun (congrFun (hM ⟨_, X7N_diag_unit s⟩) (i, j)) (k, l)
  simp only [KK, Matrix.kronecker, Matrix.diagonal_kronecker_diagonal, Matrix.mul_diagonal,
    Matrix.diagonal_mul] at this
  have := mul_left_cancel₀ hne (this.trans (mul_comm _ _))
  exact this.symm

def Pm {d : ℕ} (σ : Equiv.Perm (Fin d)) : Matrix (Fin d) (Fin d) ℂ := fun a b => if a = σ b then 1 else 0

lemma X7N_Pm_unit {d : ℕ} (σ : Equiv.Perm (Fin d)) : Pm σ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
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

lemma X7N_perm {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : ∀ V : G d, M * KK (V : Matrix (Fin d) (Fin d) ℂ) = KK (V : Matrix (Fin d) (Fin d) ℂ) * M)
    (σ : Equiv.Perm (Fin d)) (a b c e : Fin d) : M (σ a, σ b) (σ c, σ e) = M (a, b) (c, e) := by
  have := congrFun (congrFun (hM ⟨_, X7N_Pm_unit σ⟩) (σ a, σ b)) (c, e)
  simp only [KK, Matrix.kronecker, Matrix.mul_apply, Matrix.kroneckerMap_apply, Pm,
    Fintype.sum_prod_type] at this
  simp [ite_mul, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq] at this
  exact this

def ww {d : ℕ} (i0 i1 : Fin d) : Fin d → ℂ := fun k => if k = i0 then 3/5 else if k = i1 then 4/5 else 0

def Hh {d : ℕ} (i0 i1 : Fin d) : Matrix (Fin d) (Fin d) ℂ := 1 - (2 : ℂ) • Matrix.vecMulVec (ww i0 i1) (ww i0 i1)

lemma X7N_ww_star {d : ℕ} (i0 i1 : Fin d) : star (ww i0 i1) = ww i0 i1 := by
  funext k; simp only [Pi.star_apply, ww]; split_ifs <;> simp

lemma X7N_ww_dot {d : ℕ} (i0 i1 : Fin d) (h01 : i0 ≠ i1) : ww i0 i1 ⬝ᵥ ww i0 i1 = 1 := by
  have : ∀ k, ww i0 i1 k * ww i0 i1 k = (if k = i0 then (9/25 : ℂ) else 0) + (if k = i1 then (16/25 : ℂ) else 0) := by
    intro k; simp only [ww]
    by_cases h0 : k = i0
    · subst h0; simp [h01]; norm_num
    · by_cases h1 : k = i1
      · subst h1; simp [h0]; norm_num
      · simp [h0, h1]
  simp only [dotProduct, this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num

lemma X7N_Hh_unit {d : ℕ} (i0 i1 : Fin d) (h01 : i0 ≠ i1) : Hh i0 i1 ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  have hP : (Matrix.vecMulVec (ww i0 i1) (ww i0 i1))ᴴ = Matrix.vecMulVec (ww i0 i1) (ww i0 i1) := by
    rw [Matrix.conjTranspose_vecMulVec, X7N_ww_star]
  have hPP : Matrix.vecMulVec (ww i0 i1) (ww i0 i1) * Matrix.vecMulVec (ww i0 i1) (ww i0 i1) =
      Matrix.vecMulVec (ww i0 i1) (ww i0 i1) := by
    rw [Matrix.vecMulVec_mul_vecMulVec, X7N_ww_dot i0 i1 h01, one_smul]
  unfold Hh
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hP, Matrix.conjTranspose_one]
  simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hPP, smul_smul]
  have h2 : star (2 : ℂ) = 2 := by simp
  rw [h2]
  module

lemma X7N_house {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : ∀ V : G d, M * KK (V : Matrix (Fin d) (Fin d) ℂ) = KK (V : Matrix (Fin d) (Fin d) ℂ) * M)
    (i0 i1 : Fin d) (h01 : i0 ≠ i1) (z x y : ℂ)
    (hrow : ∀ q, M (i0, i0) q = if q = (i0, i0) then z else 0)
    (hcol : ∀ p, M p (i0, i1) = (if p = (i0, i1) then x else 0) + (if p = (i1, i0) then y else 0)) :
    z = x + y := by
  have := congrFun (congrFun (hM ⟨_, X7N_Hh_unit i0 i1 h01⟩) (i0, i0)) (i0, i1)
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

lemma X7N_pair {d : ℕ} (i0 i1 i j : Fin d) (h01 : i0 ≠ i1) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin d), σ i0 = i ∧ σ i1 = j := by
  refine ⟨(Equiv.swap i0 i).trans (Equiv.swap (Equiv.swap i0 i i1) j), ?_, ?_⟩
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]
    have : i ≠ Equiv.swap i0 i i1 := by
      intro h
      have : Equiv.swap i0 i i0 = Equiv.swap i0 i i1 := by rw [Equiv.swap_apply_left]; exact h
      exact h01 ((Equiv.swap i0 i).injective this)
    rw [Equiv.swap_apply_of_ne_of_ne this hij]
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]

theorem X7N_comm {d : ℕ} (hd : 2 ≤ d) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
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
    have := X7N_perm M hM (Equiv.swap i0 i) i0 i0 i0 i0
    simpa using this
  have hx : ∀ i j, i ≠ j → M (i, j) (i, j) = x := by
    intro i j hij
    obtain ⟨σ, h1, h2⟩ := X7N_pair i0 i1 i j h01 hij
    have := X7N_perm M hM σ i0 i1 i0 i1
    rwa [h1, h2] at this
  have hy : ∀ i j, i ≠ j → M (i, j) (j, i) = y := by
    intro i j hij
    obtain ⟨σ, h1, h2⟩ := X7N_pair i0 i1 i j h01 hij
    have := X7N_perm M hM σ i0 i1 i1 i0
    rwa [h1, h2] at this
  have hrow : ∀ q, M (i0, i0) q = if q = (i0, i0) then z else 0 := by
    rintro ⟨k, l⟩
    by_cases hq : (k, l) = (i0, i0)
    · rw [if_pos hq, hq]
    · rw [if_neg hq]
      by_contra hne
      rcases X7N_phase M hM i0 i0 k l hne with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;>
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
        rcases X7N_phase M hM k l i0 i1 hne with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
        · exact hq rfl
        · exact hq2 rfl
  have hz : z = x + y := X7N_house M hM i0 i1 h01 z x y hrow hcol
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
      rcases X7N_phase M hM i j k l hne with h | h
      · exact hA h
      · exact hB h

instance X7N_prob (d : ℕ) : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

lemma X7N_mapRight (d : ℕ) (g : G d) :
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

lemma X7N_intRight (d : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : G d → E) (g : G d) :
    ∫ U, f (U * g) ∂(QAlgorithms.Schur.unitaryHaar d) = ∫ U, f U ∂(QAlgorithms.Schur.unitaryHaar d) := by
  have hm : MeasurableEmbedding (· * g : G d → G d) := (MeasurableEquiv.mulRight g).measurableEmbedding
  rw [← hm.integral_map, X7N_mapRight]

lemma X7N_entry' {X : Type*} [MeasurableSpace X] {μ : Measure X} {m n : Type*} [Fintype m] [Fintype n]
    (f : X → Matrix m n ℂ) (hf : Integrable f μ) (i : m) (j : n) :
    (∫ x, f x ∂μ) i j = ∫ x, f x i j ∂μ := by
  let L : Matrix m n ℂ →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) j).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : m => (n → ℂ)) i)
  have := L.integral_comp_comm hf
  exact this.symm


lemma X7N_int_conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {m : Type*} [Fintype m]
    (A B : Matrix m m ℂ) (f : X → Matrix m m ℂ) (hf : Integrable f μ) :
    ∫ x, A * f x * B ∂μ = A * (∫ x, f x ∂μ) * B := by
  let L0 : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ :=
    { toFun := fun X => A * X * B
      map_add' := fun X Y => by simp [mul_add, add_mul]
      map_smul' := fun c X => by simp [Matrix.mul_smul, Matrix.smul_mul] }
  let L : Matrix m m ℂ →L[ℂ] Matrix m m ℂ := LinearMap.toContinuousLinearMap L0
  exact L.integral_comp_comm hf

lemma X7N_int_trace {X : Type*} [MeasurableSpace X] {μ : Measure X} {m : Type*} [Fintype m]
    (f : X → Matrix m m ℂ) (hf : Integrable f μ) :
    ∫ x, (f x).trace ∂μ = (∫ x, f x ∂μ).trace := by
  let L : Matrix m m ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap m ℂ ℂ)
  exact L.integral_comp_comm hf

def MM {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ∫ U, ff S U ∂(QAlgorithms.Schur.unitaryHaar d)

lemma X7N_MM_comm {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (V : G d) :
    MM S * KK (V : Matrix (Fin d) (Fin d) ℂ) = KK (V : Matrix (Fin d) (Fin d) ℂ) * MM S := by
  have hinv : (KK (V : Matrix (Fin d) (Fin d) ℂ))ᴴ * MM S * KK (V : Matrix (Fin d) (Fin d) ℂ) = MM S := by
    unfold MM
    rw [← X7N_int_conj _ _ _ (X7N_ff_int S)]
    have : ∀ U : G d, (KK (V : Matrix (Fin d) (Fin d) ℂ))ᴴ * ff S U * KK (V : Matrix (Fin d) (Fin d) ℂ)
        = ff S (U * V) := by
      intro U
      simp only [ff, Matrix.UnitaryGroup.mul_apply, X7N_KK_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    simp_rw [this]
    exact X7N_intRight d (ff S) V
  have hu := (X7N_KK_unit V).2
  calc MM S * KK (V : Matrix (Fin d) (Fin d) ℂ)
      = (KK (V : Matrix (Fin d) (Fin d) ℂ) * (KK (V : Matrix (Fin d) (Fin d) ℂ))ᴴ) * MM S *
          KK (V : Matrix (Fin d) (Fin d) ℂ) := by rw [hu, Matrix.one_mul]
    _ = KK (V : Matrix (Fin d) (Fin d) ℂ) * ((KK (V : Matrix (Fin d) (Fin d) ℂ))ᴴ * MM S *
          KK (V : Matrix (Fin d) (Fin d) ℂ)) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hinv]

open QAlgorithms.Papers.Independent.Dependency50.P19 in
lemma X7N_swap_KK {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : swap (Fin d) * KK U = KK U * swap (Fin d) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.mul_apply, swap, KK, Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]

lemma X7N_tr_MM {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : (MM S).trace = S.trace := by
  unfold MM
  rw [← X7N_int_trace _ (X7N_ff_int S)]
  have : ∀ U : G d, (ff S U).trace = S.trace := by
    intro U
    simp only [ff]
    rw [Matrix.trace_mul_cycle, (X7N_KK_unit U).2, Matrix.one_mul]
  simp [this]

open QAlgorithms.Papers.Independent.Dependency50.P19 in
lemma X7N_tr_MMF {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (MM S * swap (Fin d)).trace = (S * swap (Fin d)).trace := by
  have h1 : MM S * swap (Fin d) = ∫ U, 1 * ff S U * swap (Fin d) ∂(QAlgorithms.Schur.unitaryHaar d) := by
    rw [X7N_int_conj _ _ _ (X7N_ff_int S), Matrix.one_mul]; rfl
  rw [h1, ← X7N_int_trace]
  · have : ∀ U : G d, (1 * ff S U * swap (Fin d)).trace = (S * swap (Fin d)).trace := by
      intro U
      simp only [ff, Matrix.one_mul]
      have e : (KK (U : Matrix (Fin d) (Fin d) ℂ))ᴴ * S * KK (U : Matrix (Fin d) (Fin d) ℂ) * swap (Fin d)
          = (KK (U : Matrix (Fin d) (Fin d) ℂ))ᴴ * (S * swap (Fin d) * KK (U : Matrix (Fin d) (Fin d) ℂ)) := by
        rw [Matrix.mul_assoc _ (KK _), ← X7N_swap_KK]; simp only [Matrix.mul_assoc]
      rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, (X7N_KK_unit U).2, Matrix.mul_one]
    simp_rw [this]
    simp
  · exact (((continuous_const.matrix_mul (X7N_ff_cont S)).matrix_mul continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

@[simp] lemma X7N_and_symm {α : Type*} (a b : α) : (a = b ∧ b = a) ↔ a = b :=
  ⟨fun h => h.1, fun h => ⟨h, h.symm⟩⟩

open QAlgorithms.Papers.Independent.Dependency50.P19 in
lemma X7N_trace_form {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (x y : ℂ)
    (h : ∀ i j k l : Fin d, M (i, j) (k, l) = (if i = k ∧ j = l then x else 0) + (if i = l ∧ j = k then y else 0)) :
    M.trace = (d : ℂ)^2 * x + d * y ∧ (M * swap (Fin d)).trace = d * x + (d : ℂ)^2 * y := by
  constructor
  · simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, h]
    simp [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
    ring
  · simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, h, swap]
    simp [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and, add_mul]
    ring

lemma X7N_card2 {a1 a2 : ℕ} (b : Fin a2) :
    (Finset.univ.filter (fun q : Fin a1 × Fin a2 => b = q.2)).card = a1 := by
  simp only [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

lemma X7N_card1 {a1 a2 : ℕ} (b : Fin a1) :
    (Finset.univ.filter (fun q : Fin a1 × Fin a2 => b = q.1)).card = a2 := by
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp
  · intro c _ hc; simp [Ne.symm hc]
  · simp

open QAlgorithms.Papers.Independent.Dependency50.P19 in
lemma X7N_tr_S (a1 a2 : ℕ) : (swapSecond a1 a2).trace = (a1 : ℂ)^2 * a2 := by
  simp only [Matrix.trace, Matrix.diag, swapSecond, Fintype.sum_prod_type]
  rw [← (finProdFinEquiv (m := a1) (n := a2)).sum_comp]
  simp only [Equiv.symm_apply_apply]
  conv_lhs => arg 2; ext p; rw [← (finProdFinEquiv (m := a1) (n := a2)).sum_comp]
  simp [Fintype.sum_prod_type, X7N_card2]
  ring

open QAlgorithms.Papers.Independent.Dependency50.P19 in
lemma X7N_trF {X : Type*} [Fintype X] [DecidableEq X] (M : Matrix (X × X) (X × X) ℂ) :
    (M * swap X).trace = ∑ i, ∑ j, M (i, j) (j, i) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, swap, Fintype.sum_prod_type, mul_ite, mul_one,
    mul_zero, ite_and]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

open QAlgorithms.Papers.Independent.Dependency50.P19 in
lemma X7N_tr_SF (a1 a2 : ℕ) : (swapSecond a1 a2 * swap (Fin (a1 * a2))).trace = (a1 : ℂ) * (a2 : ℂ)^2 := by
  rw [X7N_trF]
  simp only [swapSecond]
  rw [← (finProdFinEquiv (m := a1) (n := a2)).sum_comp]
  simp only [Equiv.symm_apply_apply]
  conv_lhs => arg 2; ext p; rw [← (finProdFinEquiv (m := a1) (n := a2)).sum_comp]
  simp [Fintype.sum_prod_type, X7N_card1]
  ring

lemma X7N_int_kron {X : Type*} [MeasurableSpace X] {μ : Measure X} {m n : Type*} [Fintype m] [Fintype n]
    (f : X → Matrix m m ℂ) (C : Matrix n n ℂ) (hf : Integrable f μ) :
    ∫ x, Matrix.kronecker (f x) C ∂μ = Matrix.kronecker (∫ x, f x ∂μ) C := by
  let L0 : Matrix m m ℂ →ₗ[ℂ] Matrix (m × n) (m × n) ℂ :=
    { toFun := fun X => Matrix.kronecker X C
      map_add' := fun X Y => by simp [Matrix.kronecker, Matrix.add_kronecker]
      map_smul' := fun c X => by simp [Matrix.kronecker, Matrix.smul_kronecker] }
  let L : Matrix m m ℂ →L[ℂ] Matrix (m × n) (m × n) ℂ := LinearMap.toContinuousLinearMap L0
  exact L.integral_comp_comm hf

end X7N
end

 noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P19

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (a1 a2 r : ℕ) (ha1 : 0 < a1) (ha2 : 0 < a2) (hr : 0 < r) :
    (∫ U : Matrix.unitaryGroup (Fin (a1*a2)) ℂ,
      let T : Matrix ((Fin (a1*a2) × Fin (a1*a2)) × (Fin r × Fin r))
          ((Fin (a1*a2) × Fin (a1*a2)) × (Fin r × Fin r)) ℂ := Matrix.kronecker
        (Matrix.kronecker
          (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ)
          (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ))
        (1 : Matrix (Fin r × Fin r) (Fin r × Fin r) ℂ)
      Tᴴ * Matrix.kronecker (swapSecond a1 a2) (swap (Fin r)) * T
      ∂(Schur.unitaryHaar (a1*a2))) =
    Matrix.kronecker
      ((((a1 : ℝ)+(a2 : ℝ))/((a1*a2 : ℕ)+1) : ℝ) •
        ((1/2 : ℂ) • (1 + swap (Fin (a1*a2)))) +
       (((a1 : ℝ)-(a2 : ℝ))/(((a1*a2 : ℕ) : ℝ)-1) : ℝ) •
        ((1/2 : ℂ) • (1 - swap (Fin (a1*a2))))) (swap (Fin r)) := by
  have hint : ∀ U : Matrix.unitaryGroup (Fin (a1*a2)) ℂ,
      (let T : Matrix ((Fin (a1*a2) × Fin (a1*a2)) × (Fin r × Fin r))
          ((Fin (a1*a2) × Fin (a1*a2)) × (Fin r × Fin r)) ℂ := Matrix.kronecker
        (Matrix.kronecker
          (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ)
          (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ))
        (1 : Matrix (Fin r × Fin r) (Fin r × Fin r) ℂ)
      Tᴴ * Matrix.kronecker (swapSecond a1 a2) (swap (Fin r)) * T) =
      Matrix.kronecker (X7N.ff (swapSecond a1 a2) U) (swap (Fin r)) := by
    intro U
    simp only [X7N.ff, X7N.KK, Matrix.kronecker]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp
  simp_rw [hint]
  rw [X7N.X7N_int_kron _ _ (X7N.X7N_ff_int _)]
  congr 1
  change X7N.MM (swapSecond a1 a2) = _
  rcases Nat.lt_or_ge (a1*a2) 2 with hlt | hd2
  · have h1 : a1 * a2 = 1 := by
      have : 0 < a1 * a2 := Nat.mul_pos ha1 ha2
      omega
    have ha1' : a1 = 1 := Nat.eq_one_of_mul_eq_one_right h1
    have ha2' : a2 = 1 := Nat.eq_one_of_mul_eq_one_left h1
    subst ha1' ha2'
    haveI : Subsingleton (Fin (1*1)) := ⟨fun a b => Fin.ext (by omega)⟩
    ext p q
    have hpq : p = q := Subsingleton.elim _ _
    subst hpq
    have htr := X7N.X7N_tr_MM (swapSecond 1 1)
    rw [X7N.X7N_tr_S] at htr
    have : (X7N.MM (swapSecond 1 1)).trace = X7N.MM (swapSecond 1 1) p p := by
      simp only [Matrix.trace, Matrix.diag]
      exact Fintype.sum_subsingleton _ p
    rw [this] at htr
    rw [htr]
    have hp : p.1 = p.2 := Subsingleton.elim _ _
    simp [swap, Matrix.one_apply, hp]
    norm_num
  · obtain ⟨x, y, hxy⟩ := X7N.X7N_comm hd2 _ (X7N.X7N_MM_comm (swapSecond a1 a2))
    obtain ⟨t1, t2⟩ := X7N.X7N_trace_form _ x y hxy
    rw [X7N.X7N_tr_MM, X7N.X7N_tr_S] at t1
    rw [X7N.X7N_tr_MMF, X7N.X7N_tr_SF] at t2
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
    have hx : x = a2 * (a1^2 - 1) / (((a1 : ℂ) * a2)^2 - 1) := by
      rw [eq_div_iff (by
        have : ((a1 : ℂ) * a2)^2 - 1 = ((a1 : ℂ) * a2 - 1) * ((a1 : ℂ) * a2 + 1) := by ring
        rw [this]; exact mul_ne_zero hc1 hc2)]
      apply mul_left_cancel₀ hc0
      linear_combination t2 - ((a1 : ℂ) * a2) * t1
    have hy : y = a1 * (a2^2 - 1) / (((a1 : ℂ) * a2)^2 - 1) := by
      rw [eq_div_iff (by
        have : ((a1 : ℂ) * a2)^2 - 1 = ((a1 : ℂ) * a2 - 1) * ((a1 : ℂ) * a2 + 1) := by ring
        rw [this]; exact mul_ne_zero hc1 hc2)]
      apply mul_left_cancel₀ hc0
      linear_combination t1 - ((a1 : ℂ) * a2) * t2
    have hc3 : ((a1 : ℂ) * a2)^2 - 1 ≠ 0 := by
      have : ((a1 : ℂ) * a2)^2 - 1 = ((a1 : ℂ) * a2 - 1) * ((a1 : ℂ) * a2 + 1) := by ring
      rw [this]; exact mul_ne_zero hc1 hc2
    set α : ℝ := ((a1 : ℝ)+(a2 : ℝ))/((a1*a2 : ℕ)+1) with hαdef
    set β : ℝ := ((a1 : ℝ)-(a2 : ℝ))/(((a1*a2 : ℕ) : ℝ)-1) with hβdef
    have hα : (α : ℂ) = ((a1 : ℂ) + a2) / ((a1 : ℂ) * a2 + 1) := by rw [hαdef]; push_cast; ring
    have hβ : (β : ℂ) = ((a1 : ℂ) - a2) / ((a1 : ℂ) * a2 - 1) := by rw [hβdef]; push_cast; ring
    have hxα : x = ((α : ℂ) + β) / 2 := by
      rw [hx, hα, hβ, div_add_div _ _ hc2 hc1, div_div,
        div_eq_div_iff hc3 (mul_ne_zero (mul_ne_zero hc2 hc1) two_ne_zero)]; ring
    have hyβ : y = ((α : ℂ) - β) / 2 := by
      rw [hy, hα, hβ, div_sub_div _ _ hc2 hc1, div_div,
        div_eq_div_iff hc3 (mul_ne_zero (mul_ne_zero hc2 hc1) two_ne_zero)]; ring
    ext ⟨i, j⟩ ⟨k, l⟩
    rw [hxy]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, swap, Matrix.sub_apply,
      Prod.mk.injEq, smul_eq_mul, Complex.real_smul]
    rw [hxα, hyβ]
    by_cases hA : i = k ∧ j = l <;> by_cases hB : i = l ∧ j = k
    · simp only [eq_true hA, eq_true hB, if_true]; ring
    · simp only [eq_true hA, eq_false hB, if_true, if_false]; ring
    · simp only [eq_false hA, eq_true hB, if_true, if_false]; ring
    · simp only [eq_false hA, eq_false hB, if_false]; ring


end

