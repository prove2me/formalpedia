-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.iteratedFDeriv_linear_comb_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:18.81635+00:00
-- url     : https://prove2.me/submissions/f815bf96-f017-4af3-a197-a7faea01c9bc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AInterpSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseGenSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenMet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsBoundIteratedFDerivCompact

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
    (ψ₀ ψ₁ : E → ℝ) (y₀ y : E) (k : ℕ) (a₀ a₁ : ℝ)
    (h₀ : ContDiffAt ℝ k ψ₀ (y₀ + y)) (h₁ : ContDiffAt ℝ k ψ₁ (y₀ + y)) :
    iteratedFDeriv ℝ k (fun y => a₀ * ψ₀ (y₀ + y) + a₁ * ψ₁ (y₀ + y)) y =
      a₀ • iteratedFDeriv ℝ k ψ₀ (y₀ + y) + a₁ • iteratedFDeriv ℝ k ψ₁ (y₀ + y) := by
  have hshift : ∀ ψ : E → ℝ, iteratedFDeriv ℝ k (fun y => ψ (y₀ + y)) y = iteratedFDeriv ℝ k ψ (y₀ + y) := by
    intro ψ
    have := iteratedFDerivWithin_comp_add_left (𝕜 := ℝ) (f := ψ) (s := Set.univ) k y₀ y
    simpa [iteratedFDerivWithin_univ] using this
  have hc0 : ContDiffAt ℝ k (fun y => ψ₀ (y₀ + y)) y := h₀.comp y (contDiffAt_const.add contDiffAt_id)
  have hc1 : ContDiffAt ℝ k (fun y => ψ₁ (y₀ + y)) y := h₁.comp y (contDiffAt_const.add contDiffAt_id)
  have e : (fun y => a₀ * ψ₀ (y₀ + y) + a₁ * ψ₁ (y₀ + y)) =
      fun y => a₀ • (fun y => ψ₀ (y₀ + y)) y + a₁ • (fun y => ψ₁ (y₀ + y)) y := rfl
  rw [e, fun_iteratedFDeriv_add_apply (hc0.const_smul a₀) (hc1.const_smul a₁),
    iteratedFDeriv_const_smul_apply' hc0, iteratedFDeriv_const_smul_apply' hc1, hshift, hshift]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
