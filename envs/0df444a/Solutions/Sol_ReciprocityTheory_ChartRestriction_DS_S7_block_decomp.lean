-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.block_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:46.045074+00:00
-- url     : https://prove2.me/submissions/13b65bfc-87b3-42e1-9690-8b67c52670a3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
private lemma commute_Jm_of_isBlock {Y : Matrix (Fin n) (Fin n) ℂ} (hY : IsBlock ε Y) :
    Y * Jm ε = Jm ε * Y := by
  ext a b
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : ε a = ε b
  · rw [h, mul_comm]
  · simp [hY a b h]
end ReciprocityTheory.ChartRestriction.DS.S7
end
end

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsBlock ε X) :
    ∃ A B : Matrix (Fin n) (Fin n) ℂ, inK ε A ∧ inK ε B ∧ X = A + Complex.I • B ∧
      Xᴴ = -A + Complex.I • B := by
  have hXH : IsBlock ε Xᴴ := fun a b h => by
    rw [Matrix.conjTranspose_apply, hX b a (Ne.symm h), star_zero]
  have hc1 := commute_Jm_of_isBlock hX
  have hc2 := commute_Jm_of_isBlock hXH
  have hI : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I]
    norm_num
  have hIB : Complex.I • ((-Complex.I / 2) • (X + Xᴴ)) = (1 / 2 : ℂ) • (X + Xᴴ) := by
    rw [smul_smul, hI]
  have hs1 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  have hs2 : star (-Complex.I / 2) = Complex.I / 2 := by simp
  refine ⟨(1 / 2 : ℂ) • (X - Xᴴ), (-Complex.I / 2) • (X + Xᴴ), ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · unfold inG
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
      hs1, Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, hc1, hc2]
    module
  · rw [Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, hc1, hc2]
  · unfold inG
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
      hs2, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hc1, hc2]
    module
  · rw [Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hc1, hc2]
  · rw [hIB]
    module
  · rw [hIB]
    module
end ReciprocityTheory.ChartRestriction.DS.S7
