-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P23.pauli_not
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T20:08:56.796754+00:00
-- url     : https://prove2.me/submissions/1ce1d53f-f8fd-450c-8f7f-dd8922ec4cc6

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23


open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

noncomputable section
namespace X7N2

noncomputable def X7N2_cen {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) := SeminormedAddGroup.toContinuousENorm
attribute [local instance] X7N2_cen

attribute [local instance] Classical.propDecidable Classical.decEq


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

end X7N2


open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

noncomputable section
namespace X7N2
attribute [local instance] X7N2_cen

attribute [local instance] Classical.propDecidable Classical.decEq

lemma X7P_entry {X : Type*} [MeasurableSpace X] {μ : Measure X} {m n : Type*} [Fintype m] [Fintype n]
    (f : X → Matrix m n ℂ) (hf : Integrable f μ) (i : m) (j : n) :
    (∫ x, f x ∂μ) i j = ∫ x, f x i j ∂μ := by
  let L : Matrix m n ℂ →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) j).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : m => (n → ℂ)) i)
  have := L.integral_comp_comm hf
  exact this.symm

lemma X7P_int_conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {m : Type*} [Fintype m]
    (A B : Matrix m m ℂ) (f : X → Matrix m m ℂ) (hf : Integrable f μ) :
    ∫ x, A * f x * B ∂μ = A * (∫ x, f x ∂μ) * B := by
  let L0 : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ :=
    { toFun := fun X => A * X * B
      map_add' := fun X Y => by simp [mul_add, add_mul]
      map_smul' := fun c X => by simp [Matrix.mul_smul, Matrix.smul_mul] }
  let L : Matrix m m ℂ →L[ℂ] Matrix m m ℂ := LinearMap.toContinuousLinearMap L0
  exact L.integral_comp_comm hf

def S0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => if p = (0, 0) ∧ q = (0, 0) then 1 else 0

def gg (U : G 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  KK (U : Matrix (Fin 2) (Fin 2) ℂ) * S0 * (KK (U : Matrix (Fin 2) (Fin 2) ℂ))ᴴ

lemma X7P_gg_entry (U : G 2) (i a j b : Fin 2) :
    gg U (i, a) (j, b) = U i 0 * U a 0 * conj (U j 0) * conj (U b 0) := by
  simp [gg, S0, Matrix.mul_apply, KK, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  ring

lemma X7P_gg_cont : Continuous gg := by
  unfold gg
  exact ((X7N2_KK_cont 2).matrix_mul continuous_const).matrix_mul (X7N2_KK_cont 2).matrix_conjTranspose

lemma X7P_gg_int : Integrable gg (QAlgorithms.Schur.unitaryHaar 2) :=
  X7P_gg_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def NN : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := ∫ U, gg U ∂(QAlgorithms.Schur.unitaryHaar 2)

lemma X7P_NN_comm (V : G 2) :
    NN * KK (V : Matrix (Fin 2) (Fin 2) ℂ) = KK (V : Matrix (Fin 2) (Fin 2) ℂ) * NN := by
  have hinv : KK (V : Matrix (Fin 2) (Fin 2) ℂ) * NN * (KK (V : Matrix (Fin 2) (Fin 2) ℂ))ᴴ = NN := by
    unfold NN
    rw [← X7P_int_conj _ _ _ X7P_gg_int]
    have : ∀ U : G 2, KK (V : Matrix (Fin 2) (Fin 2) ℂ) * gg U * (KK (V : Matrix (Fin 2) (Fin 2) ℂ))ᴴ
        = gg (V * U) := by
      intro U
      simp only [gg, Matrix.UnitaryGroup.mul_apply, X7N2_KK_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    simp_rw [this]
    exact integral_mul_left_eq_self gg V
  have hu := (X7N2_KK_unit V).1
  calc NN * KK (V : Matrix (Fin 2) (Fin 2) ℂ)
      = (KK (V : Matrix (Fin 2) (Fin 2) ℂ) * NN * (KK (V : Matrix (Fin 2) (Fin 2) ℂ))ᴴ) *
          KK (V : Matrix (Fin 2) (Fin 2) ℂ) := by rw [hinv]
    _ = KK (V : Matrix (Fin 2) (Fin 2) ℂ) * NN * ((KK (V : Matrix (Fin 2) (Fin 2) ℂ))ᴴ *
          KK (V : Matrix (Fin 2) (Fin 2) ℂ)) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu, Matrix.mul_one]

lemma X7P_col (U : G 2) : ∑ i, U i 0 * conj (U i 0) = 1 := by
  have h1 : (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * U = 1 := Matrix.UnitaryGroup.star_mul_self U
  have := congrFun (congrFun h1 0) 0
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

lemma X7P_entry_cont (i a j b : Fin 2) :
    Continuous (fun U : G 2 => U i 0 * U a 0 * conj (U j 0) * conj (U b 0)) := by
  have h := (X7P_gg_cont.matrix_elem (i, a) (j, b))
  simpa [X7P_gg_entry] using h

lemma X7P_NN_entry (i a j b : Fin 2) :
    NN (i, a) (j, b) = ∫ U, U i 0 * U a 0 * conj (U j 0) * conj (U b 0) ∂(QAlgorithms.Schur.unitaryHaar 2) := by
  rw [NN, X7P_entry _ X7P_gg_int]
  simp only [X7P_gg_entry]

instance X7P_prob : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar 2) :=
  ⟨Measure.haarMeasure_self⟩

lemma X7P_int (f : G 2 → ℂ) (hf : Continuous f) : Integrable f (QAlgorithms.Schur.unitaryHaar 2) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma X7P_sum2 (f : Fin 2 → Fin 2 → G 2 → ℂ) (hf : ∀ i a, Continuous (f i a)) :
    ∑ i : Fin 2, ∑ a : Fin 2, ∫ U, f i a U ∂(QAlgorithms.Schur.unitaryHaar 2) =
      ∫ U, ∑ i : Fin 2, ∑ a : Fin 2, f i a U ∂(QAlgorithms.Schur.unitaryHaar 2) := by
  rw [integral_finsetSum _ (fun i _ => X7P_int _ (continuous_finsetSum _ fun a _ => hf i a))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun a _ => X7P_int _ (hf i a))]

lemma X7P_tr1 : ∑ i : Fin 2, ∑ a : Fin 2, NN (i, a) (i, a) = 1 := by
  simp only [X7P_NN_entry]
  rw [X7P_sum2 _ (fun i a => X7P_entry_cont _ _ _ _)]
  have : ∀ U : G 2, ∑ i : Fin 2, ∑ a : Fin 2, (U i 0 * U a 0 * conj (U i 0) * conj (U a 0)) = 1 := by
    intro U
    have h := X7P_col U
    calc _ = (∑ i, U i 0 * conj (U i 0)) * (∑ a, U a 0 * conj (U a 0)) := by
            rw [Finset.sum_mul_sum]; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_; ring
      _ = 1 := by rw [h, one_mul]
  simp only [this, integral_const, smul_eq_mul, mul_one, probReal_univ]
  simp

lemma X7P_tr2 : ∑ i : Fin 2, ∑ a : Fin 2, NN (i, a) (a, i) = 1 := by
  simp only [X7P_NN_entry]
  rw [X7P_sum2 _ (fun i a => X7P_entry_cont _ _ _ _)]
  have : ∀ U : G 2, ∑ i : Fin 2, ∑ a : Fin 2, (U i 0 * U a 0 * conj (U a 0) * conj (U i 0)) = 1 := by
    intro U
    have h := X7P_col U
    calc _ = (∑ i, U i 0 * conj (U i 0)) * (∑ a, U a 0 * conj (U a 0)) := by
            rw [Finset.sum_mul_sum]; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_; ring
      _ = 1 := by rw [h, one_mul]
  simp only [this, integral_const, smul_eq_mul, mul_one, probReal_univ]
  simp

lemma X7P_M2 (i a j b : Fin 2) :
    ∫ U, U i 0 * U a 0 * conj (U j 0) * conj (U b 0) ∂(QAlgorithms.Schur.unitaryHaar 2) =
      (if i = j ∧ a = b then (1/6 : ℂ) else 0) + (if i = b ∧ a = j then (1/6 : ℂ) else 0) := by
  obtain ⟨x, y, hxy⟩ := X7N2_comm (le_refl 2) NN X7P_NN_comm
  have t1 := X7P_tr1
  have t2 := X7P_tr2
  simp only [hxy, Fin.sum_univ_two] at t1 t2
  simp at t1 t2
  have hx : x = 1/6 := by linear_combination (2 * t1 - t2) / 6
  have hy : y = 1/6 := by linear_combination (2 * t2 - t1) / 6
  rw [← X7P_NN_entry, hxy, hx, hy]

end X7N2


open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

noncomputable section
namespace X7N2
attribute [local instance] X7N2_cen

attribute [local instance] Classical.propDecidable Classical.decEq

lemma X7P_M1 (i j : Fin 2) :
    ∫ U, U i 0 * conj (U j 0) ∂(QAlgorithms.Schur.unitaryHaar 2) = if i = j then (1/2 : ℂ) else 0 := by
  have e : ∀ U : G 2, U i 0 * conj (U j 0) = ∑ a : Fin 2, U i 0 * U a 0 * conj (U j 0) * conj (U a 0) := by
    intro U
    have h := X7P_col U
    calc U i 0 * conj (U j 0) = U i 0 * conj (U j 0) * ∑ a, U a 0 * conj (U a 0) := by rw [h, mul_one]
      _ = _ := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_; ring
  simp_rw [e]
  rw [integral_finsetSum _ (fun a _ => X7P_int _ (X7P_entry_cont _ _ _ _))]
  simp only [X7P_M2, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

open QAlgorithms QAlgorithms.Papers.Independent.Support21.P18 in
lemma X7P_phi (U : G 2) (i : Fin 2) :
    (act (U : Matrix (Fin 2) (Fin 2) ℂ) (ket (⟨0, by norm_num⟩ : Fin 2))) i = U i 0 := by
  simp [act, ket, Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]

open QAlgorithms QAlgorithms.Papers.Independent.Support21.P18 in
lemma X7P_sqk (φ : EuclideanSpace ℂ (Fin 2)) (k : Fin 2) : symmetricQubitKet 1 φ k = φ k := by
  fin_cases k <;> simp [symmetricQubitKet]

open QAlgorithms QAlgorithms.Papers.Independent.Support21.P18 in
lemma X7P_pt (rho : Matrix (Fin 2) (Fin 2) ℂ) (U : G 2) (a b : Fin 2) :
    (estimationWeight 1 rho (act (U : Matrix (Fin 2) (Fin 2) ℂ) (ket (⟨0, by norm_num⟩ : Fin 2))) •
      orthogonalDensity (act (U : Matrix (Fin 2) (Fin 2) ℂ) (ket (⟨0, by norm_num⟩ : Fin 2)))) a b =
    ∑ k : Fin 2, ∑ l : Fin 2, 2 * rho l k * ((if a = b then 1 else 0) * (U k 0 * conj (U l 0)) -
      U k 0 * U a 0 * conj (U l 0) * conj (U b 0)) := by
  simp only [estimationWeight, estimationEffect, orthogonalDensity, pureDensity, Matrix.smul_apply,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.smul_mul, Matrix.of_apply, Matrix.sub_apply,
    Matrix.one_apply, X7P_sqk, X7P_phi, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero]
  push_cast
  ring

end X7N2


open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

noncomputable section
namespace X7N2

attribute [local instance] Classical.propDecidable Classical.decEq

lemma X7P_entryL {X : Type*} [MeasurableSpace X] {μ : Measure X} {m : Type*} [Fintype m]
    (f : X → Matrix m m ℂ) (hf : Integrable f μ) (i j : m) :
    (∫ x, f x ∂μ) i j = ∫ x, f x i j ∂μ := by
  let L : Matrix m m ℂ →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : m => ℂ) j).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : m => (m → ℂ)) i)
  have := L.integral_comp_comm hf
  exact this.symm

open QAlgorithms QAlgorithms.Papers.Independent.Support21.P18 in
lemma X7P_cont (rho : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous (fun φ : EuclideanSpace ℂ (Fin 2) => estimationWeight 1 rho φ • orthogonalDensity φ) := by
  unfold estimationWeight estimationEffect orthogonalDensity pureDensity symmetricQubitKet
  fun_prop

open QAlgorithms QAlgorithms.Papers.Independent.Support21.P18 in
lemma X7P_main (rho : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2) :
    measurementNot 1 rho a b = ∑ k : Fin 2, ∑ l : Fin 2, 2 * rho l k *
      ((if a = b then 1 else 0) * (if k = l then (1/2 : ℂ) else 0) -
        ((if k = l ∧ a = b then (1/6 : ℂ) else 0) + (if k = b ∧ a = l then (1/6 : ℂ) else 0))) := by
  unfold measurementNot pureLaw QuditFidelity.haarPureStateLaw
  rw [integral_map (QuditFidelity.haarState_continuous 2 (by norm_num)).aemeasurable
    (X7P_cont rho).aestronglyMeasurable]
  have hc : Continuous (fun U : G 2 =>
      estimationWeight 1 rho (act (U : Matrix (Fin 2) (Fin 2) ℂ) (ket (⟨0, by norm_num⟩ : Fin 2))) •
        orthogonalDensity (act (U : Matrix (Fin 2) (Fin 2) ℂ) (ket (⟨0, by norm_num⟩ : Fin 2)))) :=
    (X7P_cont rho).comp (QuditFidelity.haarState_continuous 2 (by norm_num))
  refine (X7P_entryL _ (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) a b).trans ?_
  simp only [X7P_pt]
  have hcont : ∀ k l : Fin 2, Continuous (fun U : G 2 => 2 * rho l k * ((if a = b then 1 else 0) *
      (U k 0 * conj (U l 0)) - U k 0 * U a 0 * conj (U l 0) * conj (U b 0))) := by
    intro k l
    have h1 : Continuous (fun U : G 2 => U k 0 * conj (U l 0)) := by
      have := (continuous_subtype_val (p := fun U : Matrix (Fin 2) (Fin 2) ℂ => U ∈ Matrix.unitaryGroup (Fin 2) ℂ))
      exact (this.matrix_elem k 0).mul (Complex.continuous_conj.comp (this.matrix_elem l 0))
    exact continuous_const.mul ((continuous_const.mul h1).sub (X7P_entry_cont k a l b))
  rw [← X7P_sum2 _ hcont]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, integral_sub, integral_const_mul, X7P_M1, X7P_M2]
  · exact X7P_int _ (continuous_const.mul ((continuous_subtype_val.matrix_elem k 0).mul
      (Complex.continuous_conj.comp (continuous_subtype_val.matrix_elem l 0))))
  · exact X7P_int _ (X7P_entry_cont k a l b)

end X7N2

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P23 in
theorem solution (rho : QAlgorithms.Papers.Independent.Information100.P21.Op (Fin 2)) :
    universalNotChannel 1 rho = (1/3 : ℂ) •
      (conjSuperop (!![0,1;1,0] : QAlgorithms.Papers.Independent.Information100.P21.Op (Fin 2)) rho +
       conjSuperop (!![0,-Complex.I;Complex.I,0] : QAlgorithms.Papers.Independent.Information100.P21.Op (Fin 2)) rho +
       conjSuperop (!![1,0;0,-1] : QAlgorithms.Papers.Independent.Information100.P21.Op (Fin 2)) rho) := by
  ext a b
  rw [show universalNotChannel 1 rho a b = _ from X7N2.X7P_main rho a b]
  fin_cases a <;> fin_cases b <;>
    simp only [conjSuperop, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply] <;>
    simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring
