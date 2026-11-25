-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.iteratedFDeriv_convexComb_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:56:20.715876+00:00
-- url     : https://prove2.me/submissions/7f61d030-179b-44ac-939f-a38347d016fd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AInterpSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseGenSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenMet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsBoundIteratedFDerivCompact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_iteratedFDeriv_linear_comb_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory
open scoped ContDiff
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ₀ ψ₁ : E → ℝ) (y₀ y : E) (k : ℕ) {t B₀ B₁ : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (h₀ : ContDiffAt ℝ k ψ₀ (y₀ + y)) (h₁ : ContDiffAt ℝ k ψ₁ (y₀ + y))
    (hb₀ : ‖iteratedFDeriv ℝ k ψ₀ (y₀ + y)‖ ≤ B₀) (hb₁ : ‖iteratedFDeriv ℝ k ψ₁ (y₀ + y)‖ ≤ B₁) :
    ‖iteratedFDeriv ℝ k (fun y => (2 * (1 - t)) * ψ₀ (y₀ + y) + (2 * t) * ψ₁ (y₀ + y)) y‖ ≤
      2 * (B₀ + B₁) := by
  rw [iteratedFDeriv_linear_comb_shift ψ₀ ψ₁ y₀ y k _ _ h₀ h₁]
  obtain ⟨ht0, ht1⟩ := ht
  have n0 := norm_nonneg (iteratedFDeriv ℝ k ψ₀ (y₀ + y))
  have n1 := norm_nonneg (iteratedFDeriv ℝ k ψ₁ (y₀ + y))
  calc ‖(2 * (1 - t)) • iteratedFDeriv ℝ k ψ₀ (y₀ + y) + (2 * t) • iteratedFDeriv ℝ k ψ₁ (y₀ + y)‖
      ≤ ‖(2 * (1 - t)) • iteratedFDeriv ℝ k ψ₀ (y₀ + y)‖ + ‖(2 * t) • iteratedFDeriv ℝ k ψ₁ (y₀ + y)‖ :=
        norm_add_le _ _
    _ = (2 * (1 - t)) * ‖iteratedFDeriv ℝ k ψ₀ (y₀ + y)‖ + (2 * t) * ‖iteratedFDeriv ℝ k ψ₁ (y₀ + y)‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by linarith)]
    _ ≤ 2 * (B₀ + B₁) := by
        nlinarith [mul_le_mul_of_nonneg_left hb₀ (by linarith : (0 : ℝ) ≤ 1 - t),
          mul_le_mul_of_nonneg_left hb₁ ht0, mul_nonneg ht0 hB₀, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) hB₁]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
