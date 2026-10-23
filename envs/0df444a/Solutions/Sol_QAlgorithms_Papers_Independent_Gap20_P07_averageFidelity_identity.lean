-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P07.averageFidelity_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T20:42:14.716282+00:00
-- url     : https://prove2.me/submissions/421bcd16-ba55-4d11-9219-2808aa80b4ae

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P07

open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

noncomputable section
namespace X7UA

def swap (X : Type*) [DecidableEq X] : Matrix (X × X) (X × X) ℂ :=
  fun i j => if i.1 = j.2 ∧ i.2 = j.1 then 1 else 0

attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable instance X7UA_cen {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) := SeminormedAddGroup.toContinuousENorm

instance X7UA_haar (d : ℕ) : (QAlgorithms.Schur.unitaryHaar d).IsHaarMeasure := by
  unfold QAlgorithms.Schur.unitaryHaar; infer_instance

abbrev G (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ

def KK {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.kronecker U U

def ff {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (U : G d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (KK (U : Matrix (Fin d) (Fin d) ℂ))ᴴ * S * KK (U : Matrix (Fin d) (Fin d) ℂ)

lemma X7UA_KK_cont (d : ℕ) : Continuous (fun U : G d => KK (U : Matrix (Fin d) (Fin d) ℂ)) := by
  have hU : Continuous (fun U : G d => (U : Matrix (Fin d) (Fin d) ℂ)) := continuous_subtype_val
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [KK]
  exact (hU.matrix_elem i.1 j.1).mul (hU.matrix_elem i.2 j.2)

lemma X7UA_ff_cont {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Continuous (ff S) := by
  unfold ff
  exact ((X7UA_KK_cont d).matrix_conjTranspose.matrix_mul continuous_const).matrix_mul (X7UA_KK_cont d)

lemma X7UA_ff_int {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Integrable (ff S) (QAlgorithms.Schur.unitaryHaar d) :=
  (X7UA_ff_cont S).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma X7UA_KK_mul {d : ℕ} (U V : Matrix (Fin d) (Fin d) ℂ) : KK (U * V) = KK U * KK V := by
  unfold KK; simp only [Matrix.kronecker]; rw [Matrix.mul_kronecker_mul]

lemma X7UA_KK_unit {d : ℕ} (U : G d) : (KK (U : Matrix (Fin d) (Fin d) ℂ))ᴴ * KK (U : Matrix (Fin d) (Fin d) ℂ) = 1 ∧
    KK (U : Matrix (Fin d) (Fin d) ℂ) * (KK (U : Matrix (Fin d) (Fin d) ℂ))ᴴ = 1 := by
  have h1 : (U : Matrix (Fin d) (Fin d) ℂ)ᴴ * U = 1 := Matrix.UnitaryGroup.star_mul_self U
  have h2 : (U : Matrix (Fin d) (Fin d) ℂ) * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp U.2
    rwa [Matrix.star_eq_conjTranspose] at this
  unfold KK
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, h1, h2]
  simp


lemma X7UA_phase_aux {X : Type*} [DecidableEq X] (a b c e : X)
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

lemma X7UA_diag_unit {d : ℕ} (s : Fin d) :
    Matrix.diagonal (fun t : Fin d => if t = s then Complex.I else 1) ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1; funext t
  by_cases h : t = s <;> simp [h]

lemma X7UA_phase {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : ∀ V : G d, M * KK (V : Matrix (Fin d) (Fin d) ℂ) = KK (V : Matrix (Fin d) (Fin d) ℂ) * M)
    (i j k l : Fin d) (hne : M (i, j) (k, l) ≠ 0) : (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  apply X7UA_phase_aux
  intro s
  have := congrFun (congrFun (hM ⟨_, X7UA_diag_unit s⟩) (i, j)) (k, l)
  simp only [KK, Matrix.kronecker, Matrix.diagonal_kronecker_diagonal, Matrix.mul_diagonal,
    Matrix.diagonal_mul] at this
  have := mul_left_cancel₀ hne (this.trans (mul_comm _ _))
  exact this.symm

def Pm {d : ℕ} (σ : Equiv.Perm (Fin d)) : Matrix (Fin d) (Fin d) ℂ := fun a b => if a = σ b then 1 else 0

lemma X7UA_Pm_unit {d : ℕ} (σ : Equiv.Perm (Fin d)) : Pm σ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
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

lemma X7UA_perm {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : ∀ V : G d, M * KK (V : Matrix (Fin d) (Fin d) ℂ) = KK (V : Matrix (Fin d) (Fin d) ℂ) * M)
    (σ : Equiv.Perm (Fin d)) (a b c e : Fin d) : M (σ a, σ b) (σ c, σ e) = M (a, b) (c, e) := by
  have := congrFun (congrFun (hM ⟨_, X7UA_Pm_unit σ⟩) (σ a, σ b)) (c, e)
  simp only [KK, Matrix.kronecker, Matrix.mul_apply, Matrix.kroneckerMap_apply, Pm,
    Fintype.sum_prod_type] at this
  simp [ite_mul, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq] at this
  exact this

def ww {d : ℕ} (i0 i1 : Fin d) : Fin d → ℂ := fun k => if k = i0 then 3/5 else if k = i1 then 4/5 else 0

def Hh {d : ℕ} (i0 i1 : Fin d) : Matrix (Fin d) (Fin d) ℂ := 1 - (2 : ℂ) • Matrix.vecMulVec (ww i0 i1) (ww i0 i1)

lemma X7UA_ww_star {d : ℕ} (i0 i1 : Fin d) : star (ww i0 i1) = ww i0 i1 := by
  funext k; simp only [Pi.star_apply, ww]; split_ifs <;> simp

lemma X7UA_ww_dot {d : ℕ} (i0 i1 : Fin d) (h01 : i0 ≠ i1) : ww i0 i1 ⬝ᵥ ww i0 i1 = 1 := by
  have : ∀ k, ww i0 i1 k * ww i0 i1 k = (if k = i0 then (9/25 : ℂ) else 0) + (if k = i1 then (16/25 : ℂ) else 0) := by
    intro k; simp only [ww]
    by_cases h0 : k = i0
    · subst h0; simp [h01]; norm_num
    · by_cases h1 : k = i1
      · subst h1; simp [h0]; norm_num
      · simp [h0, h1]
  simp only [dotProduct, this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num

lemma X7UA_Hh_unit {d : ℕ} (i0 i1 : Fin d) (h01 : i0 ≠ i1) : Hh i0 i1 ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  have hP : (Matrix.vecMulVec (ww i0 i1) (ww i0 i1))ᴴ = Matrix.vecMulVec (ww i0 i1) (ww i0 i1) := by
    rw [Matrix.conjTranspose_vecMulVec, X7UA_ww_star]
  have hPP : Matrix.vecMulVec (ww i0 i1) (ww i0 i1) * Matrix.vecMulVec (ww i0 i1) (ww i0 i1) =
      Matrix.vecMulVec (ww i0 i1) (ww i0 i1) := by
    rw [Matrix.vecMulVec_mul_vecMulVec, X7UA_ww_dot i0 i1 h01, one_smul]
  unfold Hh
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hP, Matrix.conjTranspose_one]
  simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hPP, smul_smul]
  have h2 : star (2 : ℂ) = 2 := by simp
  rw [h2]
  module

lemma X7UA_house {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : ∀ V : G d, M * KK (V : Matrix (Fin d) (Fin d) ℂ) = KK (V : Matrix (Fin d) (Fin d) ℂ) * M)
    (i0 i1 : Fin d) (h01 : i0 ≠ i1) (z x y : ℂ)
    (hrow : ∀ q, M (i0, i0) q = if q = (i0, i0) then z else 0)
    (hcol : ∀ p, M p (i0, i1) = (if p = (i0, i1) then x else 0) + (if p = (i1, i0) then y else 0)) :
    z = x + y := by
  have := congrFun (congrFun (hM ⟨_, X7UA_Hh_unit i0 i1 h01⟩) (i0, i0)) (i0, i1)
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

lemma X7UA_pair {d : ℕ} (i0 i1 i j : Fin d) (h01 : i0 ≠ i1) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin d), σ i0 = i ∧ σ i1 = j := by
  refine ⟨(Equiv.swap i0 i).trans (Equiv.swap (Equiv.swap i0 i i1) j), ?_, ?_⟩
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]
    have : i ≠ Equiv.swap i0 i i1 := by
      intro h
      have : Equiv.swap i0 i i0 = Equiv.swap i0 i i1 := by rw [Equiv.swap_apply_left]; exact h
      exact h01 ((Equiv.swap i0 i).injective this)
    rw [Equiv.swap_apply_of_ne_of_ne this hij]
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]

theorem X7UA_comm {d : ℕ} (hd : 2 ≤ d) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
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
    have := X7UA_perm M hM (Equiv.swap i0 i) i0 i0 i0 i0
    simpa using this
  have hx : ∀ i j, i ≠ j → M (i, j) (i, j) = x := by
    intro i j hij
    obtain ⟨σ, h1, h2⟩ := X7UA_pair i0 i1 i j h01 hij
    have := X7UA_perm M hM σ i0 i1 i0 i1
    rwa [h1, h2] at this
  have hy : ∀ i j, i ≠ j → M (i, j) (j, i) = y := by
    intro i j hij
    obtain ⟨σ, h1, h2⟩ := X7UA_pair i0 i1 i j h01 hij
    have := X7UA_perm M hM σ i0 i1 i1 i0
    rwa [h1, h2] at this
  have hrow : ∀ q, M (i0, i0) q = if q = (i0, i0) then z else 0 := by
    rintro ⟨k, l⟩
    by_cases hq : (k, l) = (i0, i0)
    · rw [if_pos hq, hq]
    · rw [if_neg hq]
      by_contra hne
      rcases X7UA_phase M hM i0 i0 k l hne with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;>
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
        rcases X7UA_phase M hM k l i0 i1 hne with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
        · exact hq rfl
        · exact hq2 rfl
  have hz : z = x + y := X7UA_house M hM i0 i1 h01 z x y hrow hcol
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
      rcases X7UA_phase M hM i j k l hne with h | h
      · exact hA h
      · exact hB h

instance X7UA_prob (d : ℕ) : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

lemma X7UA_mapRight (d : ℕ) (g : G d) :
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

lemma X7UA_intRight (d : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : G d → E) (g : G d) :
    ∫ U, f (U * g) ∂(QAlgorithms.Schur.unitaryHaar d) = ∫ U, f U ∂(QAlgorithms.Schur.unitaryHaar d) := by
  have hm : MeasurableEmbedding (· * g : G d → G d) := (MeasurableEquiv.mulRight g).measurableEmbedding
  rw [← hm.integral_map, X7UA_mapRight]

lemma X7UA_entry' {X : Type*} [MeasurableSpace X] {μ : Measure X} {m n : Type*} [Fintype m] [Fintype n]
    (f : X → Matrix m n ℂ) (hf : Integrable f μ) (i : m) (j : n) :
    (∫ x, f x ∂μ) i j = ∫ x, f x i j ∂μ := by
  let L : Matrix m n ℂ →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) j).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : m => (n → ℂ)) i)
  have := L.integral_comp_comm hf
  exact this.symm


lemma X7UA_int_conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {m : Type*} [Fintype m]
    (A B : Matrix m m ℂ) (f : X → Matrix m m ℂ) (hf : Integrable f μ) :
    ∫ x, A * f x * B ∂μ = A * (∫ x, f x ∂μ) * B := by
  let L0 : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ :=
    { toFun := fun X => A * X * B
      map_add' := fun X Y => by simp [mul_add, add_mul]
      map_smul' := fun c X => by simp [Matrix.mul_smul, Matrix.smul_mul] }
  let L : Matrix m m ℂ →L[ℂ] Matrix m m ℂ := LinearMap.toContinuousLinearMap L0
  exact L.integral_comp_comm hf

lemma X7UA_int_trace {X : Type*} [MeasurableSpace X] {μ : Measure X} {m : Type*} [Fintype m]
    (f : X → Matrix m m ℂ) (hf : Integrable f μ) :
    ∫ x, (f x).trace ∂μ = (∫ x, f x ∂μ).trace := by
  let L : Matrix m m ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap m ℂ ℂ)
  exact L.integral_comp_comm hf

def MM {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ∫ U, ff S U ∂(QAlgorithms.Schur.unitaryHaar d)

lemma X7UA_MM_comm {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (V : G d) :
    MM S * KK (V : Matrix (Fin d) (Fin d) ℂ) = KK (V : Matrix (Fin d) (Fin d) ℂ) * MM S := by
  have hinv : (KK (V : Matrix (Fin d) (Fin d) ℂ))ᴴ * MM S * KK (V : Matrix (Fin d) (Fin d) ℂ) = MM S := by
    unfold MM
    rw [← X7UA_int_conj _ _ _ (X7UA_ff_int S)]
    have : ∀ U : G d, (KK (V : Matrix (Fin d) (Fin d) ℂ))ᴴ * ff S U * KK (V : Matrix (Fin d) (Fin d) ℂ)
        = ff S (U * V) := by
      intro U
      simp only [ff, Matrix.UnitaryGroup.mul_apply, X7UA_KK_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    simp_rw [this]
    exact X7UA_intRight d (ff S) V
  have hu := (X7UA_KK_unit V).2
  calc MM S * KK (V : Matrix (Fin d) (Fin d) ℂ)
      = (KK (V : Matrix (Fin d) (Fin d) ℂ) * (KK (V : Matrix (Fin d) (Fin d) ℂ))ᴴ) * MM S *
          KK (V : Matrix (Fin d) (Fin d) ℂ) := by rw [hu, Matrix.one_mul]
    _ = KK (V : Matrix (Fin d) (Fin d) ℂ) * ((KK (V : Matrix (Fin d) (Fin d) ℂ))ᴴ * MM S *
          KK (V : Matrix (Fin d) (Fin d) ℂ)) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hinv]

lemma X7UA_swap_KK {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : swap (Fin d) * KK U = KK U * swap (Fin d) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.mul_apply, swap, KK, Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]

lemma X7UA_tr_MM {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : (MM S).trace = S.trace := by
  unfold MM
  rw [← X7UA_int_trace _ (X7UA_ff_int S)]
  have : ∀ U : G d, (ff S U).trace = S.trace := by
    intro U
    simp only [ff]
    rw [Matrix.trace_mul_cycle, (X7UA_KK_unit U).2, Matrix.one_mul]
  simp [this]

lemma X7UA_tr_MMF {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (MM S * swap (Fin d)).trace = (S * swap (Fin d)).trace := by
  have h1 : MM S * swap (Fin d) = ∫ U, 1 * ff S U * swap (Fin d) ∂(QAlgorithms.Schur.unitaryHaar d) := by
    rw [X7UA_int_conj _ _ _ (X7UA_ff_int S), Matrix.one_mul]; rfl
  rw [h1, ← X7UA_int_trace]
  · have : ∀ U : G d, (1 * ff S U * swap (Fin d)).trace = (S * swap (Fin d)).trace := by
      intro U
      simp only [ff, Matrix.one_mul]
      have e : (KK (U : Matrix (Fin d) (Fin d) ℂ))ᴴ * S * KK (U : Matrix (Fin d) (Fin d) ℂ) * swap (Fin d)
          = (KK (U : Matrix (Fin d) (Fin d) ℂ))ᴴ * (S * swap (Fin d) * KK (U : Matrix (Fin d) (Fin d) ℂ)) := by
        rw [Matrix.mul_assoc _ (KK _), ← X7UA_swap_KK]; simp only [Matrix.mul_assoc]
      rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, (X7UA_KK_unit U).2, Matrix.mul_one]
    simp_rw [this]
    simp
  · exact (((continuous_const.matrix_mul (X7UA_ff_cont S)).matrix_mul continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

@[simp] lemma X7UA_and_symm {α : Type*} (a b : α) : (a = b ∧ b = a) ↔ a = b :=
  ⟨fun h => h.1, fun h => ⟨h, h.symm⟩⟩

lemma X7UA_trace_form {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (x y : ℂ)
    (h : ∀ i j k l : Fin d, M (i, j) (k, l) = (if i = k ∧ j = l then x else 0) + (if i = l ∧ j = k then y else 0)) :
    M.trace = (d : ℂ)^2 * x + d * y ∧ (M * swap (Fin d)).trace = d * x + (d : ℂ)^2 * y := by
  constructor
  · simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, h]
    simp [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
    ring
  · simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, h, swap]
    simp [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and, add_mul]
    ring

open QAlgorithms

lemma X7UA_comm_all {d : ℕ} (hd : 0 < d) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : ∀ V : G d, M * KK (V : Matrix (Fin d) (Fin d) ℂ) = KK (V : Matrix (Fin d) (Fin d) ℂ) * M) :
    ∃ x y : ℂ, ∀ i j k l : Fin d,
      M (i, j) (k, l) = (if i = k ∧ j = l then x else 0) + (if i = l ∧ j = k then y else 0) := by
  by_cases h2 : 2 ≤ d
  · exact X7UA_comm h2 M hM
  · have hd1 : d = 1 := by omega
    subst hd1
    refine ⟨M (0, 0) (0, 0), 0, fun i j k l => ?_⟩
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    have hk : k = 0 := Subsingleton.elim _ _
    have hl : l = 0 := Subsingleton.elim _ _
    subst hi hj hk hl
    simp

lemma X7UA_MM00 {d : ℕ} (hd : 0 < d) (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    MM S (⟨0, hd⟩, ⟨0, hd⟩) (⟨0, hd⟩, ⟨0, hd⟩) =
      (S.trace + (S * swap (Fin d)).trace) / ((d : ℂ) * (d + 1)) := by
  obtain ⟨x, y, hxy⟩ := X7UA_comm_all hd _ (X7UA_MM_comm S)
  obtain ⟨t1, t2⟩ := X7UA_trace_form _ x y hxy
  rw [X7UA_tr_MM] at t1
  rw [X7UA_tr_MMF] at t2
  rw [hxy]
  simp only [and_self, if_true]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hd1 : (d : ℂ) + 1 ≠ 0 := by
    have : ((d : ℝ) + 1 : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  rw [eq_div_iff (mul_ne_zero hd0 hd1), t1, t2]
  ring

end X7UA

noncomputable section
namespace X7UA

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

lemma X7UA_lin {d : ℕ} (T : Superop (Fin d) (Fin d)) (hT : IsChannel T) (X : Matrix (Fin d) (Fin d) ℂ) :
    T X = ∑ j, ∑ l, X j l • T (Matrix.single j l 1) := by
  obtain ⟨m, K, _, hTK⟩ := hT
  simp only [hTK]
  unfold krausApply
  have h : ∀ j l, Matrix.single j l (X j l) = X j l • Matrix.single j l (1 : ℂ) := by
    intro j l; simp [Matrix.smul_single]
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [h, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

lemma X7UA_tp {d : ℕ} (T : Superop (Fin d) (Fin d)) (hT : IsChannel T) (X : Matrix (Fin d) (Fin d) ℂ) :
    (T X).trace = X.trace := by
  obtain ⟨m, K, hK, hTK⟩ := hT
  rw [hTK]
  unfold krausApply
  rw [Matrix.trace_sum]
  have : ∀ j, (K j * X * (K j)ᴴ).trace = ((K j)ᴴ * K j * X).trace := by
    intro j
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp only [this, ← Matrix.trace_sum, ← Finset.sum_mul]
  unfold IsKrausFamily at hK
  rw [hK, Matrix.one_mul]

lemma X7UA_psi {d : ℕ} (hd : 0 < d) (U : Matrix (Fin d) (Fin d) ℂ) (a : Fin d) :
    (act U (ket (⟨0, hd⟩ : Fin d))) a = U a ⟨0, hd⟩ := by
  simp [act, ket, Matrix.mulVec, dotProduct, PiLp.single_apply]

def SS {d : ℕ} (T : Superop (Fin d) (Fin d)) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.of fun p q => T (Matrix.single q.1 p.2 1) p.1 q.2

lemma X7UA_point {d : ℕ} (hd : 0 < d) (T : Superop (Fin d) (Fin d)) (hT : IsChannel T) (U : G d) :
    (pureDensity (act (U : Matrix (Fin d) (Fin d) ℂ) (ket (⟨0, hd⟩ : Fin d))) *
      T (pureDensity (act (U : Matrix (Fin d) (Fin d) ℂ) (ket (⟨0, hd⟩ : Fin d))))).trace =
    ff (SS T) U (⟨0, hd⟩, ⟨0, hd⟩) (⟨0, hd⟩, ⟨0, hd⟩) := by
  rw [X7UA_lin T hT]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply, X7UA_psi,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, ff, KK, Matrix.conjTranspose_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, SS, star_mul',
    RCLike.star_def, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i1 _ => ?_
  ring

lemma X7UA_avg {d : ℕ} (hd : 0 < d) (T : Superop (Fin d) (Fin d)) (hT : IsChannel T) :
    QuditFidelity.averageFidelity d hd T = (MM (SS T) (⟨0, hd⟩, ⟨0, hd⟩) (⟨0, hd⟩, ⟨0, hd⟩)).re := by
  have hc : Continuous (fun ψ : EuclideanSpace ℂ (Fin d) =>
      effectProb (pureDensity ψ) (T (pureDensity ψ))) := by
    have hp : Continuous (fun ψ : EuclideanSpace ℂ (Fin d) => pureDensity ψ) := by
      refine continuous_pi fun a => continuous_pi fun b => ?_
      simp only [pureDensity, Matrix.of_apply]
      exact ((PiLp.continuous_apply 2 _ a).mul
        (Complex.continuous_conj.comp (PiLp.continuous_apply 2 _ b)))
    unfold effectProb
    exact Complex.continuous_re.comp
      ((hp.matrix_mul ((QuditFidelity.channel_continuous T hT).comp hp)).matrix_trace)
  unfold QuditFidelity.averageFidelity QuditFidelity.haarPureStateLaw
  rw [integral_map (QuditFidelity.haarState_continuous d hd).aemeasurable hc.aestronglyMeasurable]
  unfold effectProb
  simp only [X7UA_point hd T hT]
  unfold MM
  rw [X7UA_entry' _ (X7UA_ff_int (SS T))]
  have hi : Integrable (fun U : G d => ff (SS T) U (⟨0, hd⟩, ⟨0, hd⟩) (⟨0, hd⟩, ⟨0, hd⟩))
      (QAlgorithms.Schur.unitaryHaar d) :=
    ((X7UA_ff_cont (SS T)).matrix_elem _ _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact (Complex.reCLM.integral_comp_comm hi)

lemma X7UA_trSF {d : ℕ} (T : Superop (Fin d) (Fin d)) (hT : IsChannel T) :
    (SS T * swap (Fin d)).trace = d := by
  have h1 : (SS T * swap (Fin d)).trace = ∑ a, ∑ b, T (Matrix.single b b 1) a a := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, swap, SS, Matrix.of_apply,
      Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, ite_and]
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  rw [h1, Finset.sum_comm]
  have h2 : ∀ b : Fin d, ∑ a, T (Matrix.single b b 1) a a = 1 := by
    intro b
    have := X7UA_tp T hT (Matrix.single b b 1)
    simpa [Matrix.trace] using this
  simp [h2]

lemma X7UA_ent {d : ℕ} (hd : 0 < d) (T : Superop (Fin d) (Fin d)) (hT : IsChannel T) :
    QuditFidelity.entanglementFidelity d hd T = ((SS T).trace).re / (d : ℝ)^2 := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hsm : ∀ (c : ℂ) (X : Matrix (Fin d) (Fin d) ℂ), T (c • X) = c • T X := by
    intro c X
    rw [X7UA_lin T hT (c • X), X7UA_lin T hT X, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul, mul_smul]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hsq : ((Real.sqrt d : ℂ))⁻¹ * ((Real.sqrt d : ℂ))⁻¹ = ((1 / (d : ℝ) : ℝ) : ℂ) := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
    push_cast; ring
  have hblock : ∀ a b : Fin d, (Matrix.of fun i i' =>
      pureDensity (finiteMaxEntangled (Fin d)) (a, i) (b, i')) =
      ((1 / (d : ℝ) : ℝ) : ℂ) • Matrix.single a b (1 : ℂ) := by
    intro a b
    ext i i'
    simp only [pureDensity, finiteMaxEntangled, Matrix.of_apply, Matrix.smul_apply,
      Matrix.single_apply, Fintype.card_fin, smul_eq_mul]
    by_cases h1 : a = i <;> by_cases h2 : b = i' <;> simp [h1, h2, hsq]
  unfold QuditFidelity.entanglementFidelity effectProb
  have hP : ∀ p q : Fin d × Fin d, pureDensity (finiteMaxEntangled (Fin d)) p q =
      if p.1 = p.2 ∧ q.1 = q.2 then ((1 / (d : ℝ) : ℝ) : ℂ) else 0 := by
    intro p q
    simp only [pureDensity, finiteMaxEntangled, Matrix.of_apply, Fintype.card_fin]
    by_cases h1 : p.1 = p.2 <;> by_cases h2 : q.1 = q.2 <;> simp [h1, h2, hsq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, idTensorSuperop, Matrix.of_apply,
    hblock, hsm, Matrix.smul_apply, smul_eq_mul]
  simp only [hP, Fintype.sum_prod_type, ite_and, ite_mul, zero_mul]
  simp only [SS, Matrix.of_apply]
  set c : ℂ := ((1 / (d : ℝ) : ℝ) : ℂ) with hc
  have hinner : ∀ x : Fin d, (∑ x_1, ∑ x_2, ∑ x_3, if x = x_1 then (if x_2 = x_3 then
      c * (c * T (Matrix.single x_2 x 1) x_3 x_1) else 0) else 0) =
      ∑ x_2, c * (c * T (Matrix.single x_2 x 1) x_2 x) := by
    intro x
    rw [Finset.sum_eq_single x (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp only [if_true]
    refine Finset.sum_congr rfl fun x2 _ => ?_
    rw [Finset.sum_eq_single x2 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  rw [Finset.sum_congr rfl fun x _ => hinner x]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_comm (f := fun x x_2 => T (Matrix.single x_2 x 1) x_2 x)]
  rw [← mul_assoc, hc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  field_simp

end X7UA

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms X7UA in
theorem solution (d : ℕ) (hd : 0 < d)
    (T : Superop (Fin d) (Fin d)) (hT : IsChannel T) :
    QuditFidelity.averageFidelity d hd T =
      ((d : ℝ) * QuditFidelity.entanglementFidelity d hd T + 1) / (d + 1 : ℝ) := by
  rw [X7UA_avg hd T hT, X7UA_MM00 hd, X7UA_trSF T hT, X7UA_ent hd T hT]
  have hden : ((d : ℂ) * (d + 1)) = (((d : ℝ) * (d + 1) : ℝ) : ℂ) := by push_cast; ring
  rw [hden, Complex.div_ofReal_re, Complex.add_re, Complex.natCast_re]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
  field_simp

end
