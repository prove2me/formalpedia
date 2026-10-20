-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P28.positive_map_can_have_nonpositive_unital_part
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:47:56.050128+00:00
-- url     : https://prove2.me/submissions/df7a040e-0d7a-40e9-b7a9-19c736052070

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P28

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin schattenNorm)
open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)
open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)
open QAlgorithms.Papers.Independent.Dependency50.P11 (IsUnital)

/-- the map A ↦ A₀₀ |1⟩⟨1| + (A₁₁ + A₂₂) |0⟩⟨0| -/
def g52_T : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ where
  toFun A := A 0 0 • Matrix.single 1 1 1 + (A 1 1 + A 2 2) • Matrix.single 0 0 1
  map_add' A B := by
    simp only [Matrix.add_apply, add_smul]; abel
  map_smul' c A := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul, mul_add]

lemma g52_single_psd (i : Fin 3) : (Matrix.single i i (1 : ℂ)).PosSemidef := by
  have : Matrix.single i i (1 : ℂ) = Matrix.vecMulVec (Pi.single i 1) (star (Pi.single i 1)) := by
    ext a b
    simp [Matrix.single_apply, Matrix.vecMulVec_apply, Pi.single_apply]
    by_cases ha : i = a <;> by_cases hb : i = b <;> simp [ha, hb, eq_comm]
  rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _

open QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Frontier30
  QAlgorithms.Papers.Independent.Frontier30.P28 in
theorem solution :
    ∃ n : ℕ, 3 ≤ n ∧ ∃ T : Lin n n,
      IsPositiveMap T ∧ TracePreserving T ∧ ¬ IsPositiveMap (unitalPart T) := by
  refine ⟨3, le_rfl, g52_T, ?_, ?_, ?_⟩
  · intro A hA
    have h0 := hA.diag_nonneg (i := 0)
    have h1 := hA.diag_nonneg (i := 1)
    have h2 := hA.diag_nonneg (i := 2)
    exact ((g52_single_psd 1).smul h0).add ((g52_single_psd 0).smul (add_nonneg h1 h2))
  · intro A
    simp [g52_T, Matrix.trace, Fin.sum_univ_three, Matrix.single_apply]
    ring
  · intro h
    have hP := h _ (g52_single_psd 0)
    have := hP.diag_nonneg (i := 0)
    have e : (unitalPart g52_T (Matrix.single 0 0 1)) 0 0 = -1/3 := by
      simp [unitalPart, traceTerm, nonunitalOffset, g52_T, Matrix.trace, Fin.sum_univ_three,
        Matrix.single_apply]
      norm_num
    rw [e] at this
    norm_num [Complex.le_def] at this
