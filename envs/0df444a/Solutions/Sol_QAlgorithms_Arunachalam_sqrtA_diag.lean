-- Prove2me | solution 1 for QAlgorithms.Arunachalam.sqrtA_diag
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T08:26:25.140333+00:00
-- url     : https://prove2.me/submissions/dd0acfda-a0cf-42c0-8b39-b8dec7af2216

import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Theorems.Thm_QAlgorithms_Arunachalam_fourier_comp_matrix
import Mathlib.LinearAlgebra.Eigenspace.Matrix

set_option autoImplicit false
open scoped BigOperators
open QAlgorithms

private def sg (a : ZMod 2) : ℝ := (-1 : ℝ) ^ a.val

private lemma bits (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : a.val = 0 ∨ a.val = 1 := by have := ZMod.val_lt a; omega
  rcases h with h | h
  · exact Or.inl ((ZMod.val_eq_zero a).mp h)
  · exact Or.inr ((ZMod.val_injective 2) (by simpa only [ZMod.val_one_eq_one_mod] using h))

private lemma sg_add (a b : ZMod 2) : sg (a + b) = sg a * sg b := by
  have h : (1 + 1 : ZMod 2) = 0 := by decide
  rcases bits a with rfl | rfl <;> rcases bits b with rfl | rfl <;>
    norm_num [sg, h, ZMod.val_zero, ZMod.val_one_eq_one_mod, ZMod.val_two_eq_two_mod]

private lemma two_add (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma vec_two_add {n : ℕ} (a : Fin n → ZMod 2) : a + a = 0 := by
  ext i
  exact two_add (a i)

private lemma add_zero_iff {n : ℕ} (a b : Fin n → ZMod 2) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    have := congrArg (fun x => x + b) h
    simpa only [add_assoc, vec_two_add, add_zero, zero_add] using this
  · rintro rfl
    exact vec_two_add a

private lemma char_sum {n : ℕ} (a : Fin n → ZMod 2) :
    (∑ x : Fin n → ZMod 2, sg (a ⬝ᵥ x)) = if a = 0 then (2 : ℝ)^n else 0 := by
  classical
  by_cases ha : a = 0
  · subst a
    simp [sg]
  · obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra! h
      exact ha (funext h)
    have hai : a i = 1 := by
      exact (bits (a i)).resolve_left hi
    have shift : (∑ x : Fin n → ZMod 2,
        sg (a ⬝ᵥ (x + (Pi.single i 1 : Fin n → ZMod 2)))) =
        ∑ x : Fin n → ZMod 2, sg (a ⬝ᵥ x) :=
      Equiv.sum_comp (Equiv.addRight (Pi.single i 1 : Fin n → ZMod 2))
        (fun x : Fin n → ZMod 2 => sg (a ⬝ᵥ x))
    have hs : (∑ x : Fin n → ZMod 2, sg (a ⬝ᵥ (x + Pi.single i 1))) =
        -(∑ x : Fin n → ZMod 2, sg (a ⬝ᵥ x)) := by
      simp_rw [dotProduct_add, dotProduct_single, mul_one, hai, sg_add]
      norm_num [sg, ZMod.val_one_eq_one_mod, Finset.sum_neg_distrib]
    rw [hs] at shift
    rw [if_neg ha]
    linarith

private lemma char_orth {n : ℕ} (a b : Fin n → ZMod 2) :
    (∑ x : Fin n → ZMod 2, sg (a ⬝ᵥ x) * sg (b ⬝ᵥ x)) =
      if a = b then (2 : ℝ)^n else 0 := by
  simp_rw [← sg_add, ← add_dotProduct]
  rw [char_sum]
  simp only [add_zero_iff]

private def had {k : ℕ} : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ :=
  Matrix.of fun x Q => sg (x ⬝ᵥ Q)

private lemma had_square {k : ℕ} :
    (had : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ) * had =
      (2 : ℝ)^k • 1 := by
  classical
  ext x y
  change (∑ z : Fin k → ZMod 2, sg (x ⬝ᵥ z) * sg (z ⬝ᵥ y)) = _
  simp_rw [dotProduct_comm _ y]
  rw [char_orth]
  by_cases h : x = y <;> simp [h]

private lemma conv_had {k : ℕ} (g : (Fin k → ZMod 2) → ℝ) :
    xorConvMatrix g * had = had * Matrix.diagonal (fun Q => (2 : ℝ)^k * boolFourier g Q) := by
  classical
  ext x Q
  have shift := Equiv.sum_comp (Equiv.addRight x)
    (fun z : Fin k → ZMod 2 => g z * sg (z ⬝ᵥ Q))
  have hs : (∑ y : Fin k → ZMod 2, g (x+y) * sg (y ⬝ᵥ Q)) =
      sg (x ⬝ᵥ Q) * ∑ z : Fin k → ZMod 2, g z * sg (z ⬝ᵥ Q) := by
    calc
      _ = ∑ y : Fin k → ZMod 2,
          sg (x ⬝ᵥ Q) * (g (y+x) * sg ((y+x) ⬝ᵥ Q)) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [add_dotProduct, sg_add]
        have hsq : sg (x ⬝ᵥ Q) * sg (x ⬝ᵥ Q) = 1 := by
          rw [← sg_add, two_add]
          norm_num [sg]
        rw [add_comm x y]
        calc
          _ = (g (y+x) * sg (y ⬝ᵥ Q)) * (sg (x ⬝ᵥ Q) * sg (x ⬝ᵥ Q)) := by rw [hsq, mul_one]
          _ = _ := by ring
      _ = _ := by
        rw [← Finset.mul_sum]
        exact congrArg (fun t : ℝ => sg (x ⬝ᵥ Q) * t) shift
  change (∑ y : Fin k → ZMod 2, g (x+y) * sg (y ⬝ᵥ Q)) = _
  rw [hs, Matrix.mul_diagonal]
  change sg (x ⬝ᵥ Q) * _ = sg (x ⬝ᵥ Q) * ((2 : ℝ)^k *
    (((2 : ℝ)^k)⁻¹ * ∑ z, g z * sg (Q ⬝ᵥ z)))
  simp_rw [dotProduct_comm Q]
  field_simp

private def diagHom {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (ι → ℝ) →⋆ₐ[ℝ] Matrix ι ι ℝ where
  __ := Matrix.diagonalAlgHom (n := ι) ℝ
  map_star' v := by
    ext i j
    by_cases h : i = j
    · subst j; simp
    · simp [h, Ne.symm h]

private lemma cfc_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) :
    cfc Real.sqrt (Matrix.diagonal v) = Matrix.diagonal (fun i => Real.sqrt (v i)) := by
  classical
  let ev : C(spectrum ℝ (Matrix.diagonal v), ℝ) →⋆ₐ[ℝ] (ι → ℝ) :=
    { toFun := fun f i => f ⟨v i, spectrum_diagonal v ▸ Set.mem_range_self i⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl
      map_star' := fun _ => rfl }
  let φ := (diagHom (ι := ι)).comp ev
  have hcont : Continuous φ := by
    apply Continuous.matrix_diagonal
    apply continuous_pi
    intro i
    exact continuous_eval_const _
  have hid : φ (.restrict _ (.id ℝ)) = Matrix.diagonal v := rfl
  have hd := (Matrix.isHermitian_diagonal v).isSelfAdjoint
  have heq := cfcHom_eq_of_continuous_of_map_id hd φ hcont hid
  rw [cfc_apply Real.sqrt (Matrix.diagonal v) hd (by fun_prop), heq]
  rfl

private lemma had_star {k : ℕ} :
    star (had : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ) = had := by
  ext x y
  simp [had, dotProduct_comm]

private lemma normalized_unitary {k : ℕ} :
    (Real.sqrt ((2 : ℝ)^k))⁻¹ • (had : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ)
      ∈ unitary (Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ) := by
  have hn : (2 : ℝ)^k ≠ 0 := by positivity
  have hc : (Real.sqrt ((2 : ℝ)^k))⁻¹ * (Real.sqrt ((2 : ℝ)^k))⁻¹ * (2 : ℝ)^k = 1 := by
    rw [← mul_inv, ← pow_two, Real.sq_sqrt (by positivity)]
    exact inv_mul_cancel₀ hn
  rw [Unitary.mem_iff]
  simp only [star_smul, star_trivial, had_star, Matrix.smul_mul, Matrix.mul_smul,
    had_square, smul_smul, ← mul_assoc, hc, one_smul, and_self]
private lemma sqrt_conv_diag {k : ℕ} (g : (Fin k → ZMod 2) → ℝ)
    (x : Fin k → ZMod 2) :
    psdSqrt (xorConvMatrix g) x x =
      (Real.sqrt ((2 : ℝ)^k))⁻¹ * ∑ Q, Real.sqrt (boolFourier g Q) := by
  classical
  let U : unitary (Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ) :=
    ⟨(Real.sqrt ((2 : ℝ)^k))⁻¹ • had, normalized_unitary⟩
  let d := fun Q => (2 : ℝ)^k * boolFourier g Q
  have hAU : xorConvMatrix g * (U : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ) = (U : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ) * Matrix.diagonal d := by
    change xorConvMatrix g * ((Real.sqrt ((2 : ℝ)^k))⁻¹ • had) =
      ((Real.sqrt ((2 : ℝ)^k))⁻¹ • had) * Matrix.diagonal d
    rw [Matrix.mul_smul, Matrix.smul_mul, conv_had g]
  have hA : xorConvMatrix g = (U : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ) * Matrix.diagonal d * star (U : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ) := by
    rw [← hAU, mul_assoc, Unitary.mul_star_self_of_mem U.property, mul_one]
  have hself : IsSelfAdjoint (xorConvMatrix g) := by
    ext y z
    simp [xorConvMatrix, add_comm]
  let φ := Unitary.conjStarAlgAut ℝ (Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ) U
  have hconj : φ (Matrix.diagonal d) = xorConvMatrix g := hA.symm
  have hcfc := StarAlgHomClass.map_cfc (S := ℝ) φ Real.sqrt (Matrix.diagonal d)
    (by fun_prop) (by
      change Continuous (fun B : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ =>
        (U : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ) * B * star (U : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ))
      fun_prop)
    (Matrix.isHermitian_diagonal d).isSelfAdjoint
    (hconj.symm ▸ hself)
  rw [hconj, cfc_diagonal] at hcfc
  change cfc Real.sqrt (xorConvMatrix g) x x = _
  rw [← hcfc]
  change ((U : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ) * Matrix.diagonal (fun Q => Real.sqrt (d Q)) *
    star (U : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ)) x x = _
  rw [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q _
  rw [Matrix.mul_diagonal]
  change (((Real.sqrt ((2 : ℝ)^k))⁻¹ * sg (x ⬝ᵥ Q)) * Real.sqrt (d Q)) *
    ((Real.sqrt ((2 : ℝ)^k))⁻¹ * sg (x ⬝ᵥ Q)) =
    (Real.sqrt ((2 : ℝ)^k))⁻¹ * Real.sqrt (boolFourier g Q)
  have hs : sg (x ⬝ᵥ Q) * sg (x ⬝ᵥ Q) = 1 := by
    rw [← sg_add, two_add]
    norm_num [sg]
  have hn : Real.sqrt ((2 : ℝ)^k) ≠ 0 := by positivity
  dsimp only [d]
  rw [Real.sqrt_mul (by positivity)]
  calc
    _ = ((Real.sqrt ((2 : ℝ)^k))⁻¹ * Real.sqrt (boolFourier g Q)) *
        ((Real.sqrt ((2 : ℝ)^k))⁻¹ * Real.sqrt ((2 : ℝ)^k)) *
        (sg (x ⬝ᵥ Q) * sg (x ⬝ᵥ Q)) := by ring
    _ = _ := by rw [hs, inv_mul_cancel₀ hn]; ring

theorem solution {m k T : ℕ} {β : ℝ} (_hm : 10 ≤ m) (_hβ : 0 < β) (_hβ1 : β ≤ 1)
    (_hT : 1 ≤ T) (_hTm : (T : ℝ) ≤ (m : ℝ) / (Real.exp 3 * β)) (_hk : k ≤ m)
    (M : Matrix (Fin m) (Fin k) (ZMod 2)) (_hM : M.rank = k) (x : Fin k → ZMod 2) :
    psdSqrt (xorConvMatrix fun z => weightPowFun m β T (M.mulVec z)) x x =
      (Real.sqrt ((2 : ℝ) ^ k))⁻¹ *
        ∑ Q : Fin k → ZMod 2, Real.sqrt
          (∑ S ∈ Finset.univ.filter (fun S : Fin m → ZMod 2 => M.transpose.mulVec S = Q),
            boolFourier (weightPowFun m β T) S) := by
  rw [sqrt_conv_diag]
  simp_rw [QAlgorithms.Arunachalam.fourier_comp_matrix]
