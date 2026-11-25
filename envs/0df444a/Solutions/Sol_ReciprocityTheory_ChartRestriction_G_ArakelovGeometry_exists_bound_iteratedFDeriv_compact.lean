-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_bound_iteratedFDeriv_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:42:33.236166+00:00
-- url     : https://prove2.me/submissions/af50691a-d1df-4edc-9e7a-ddb2094c3504

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AInterpSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseGenSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenMet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsBoundIteratedFDerivCompact
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono


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
    {f : E → ℝ} {U K : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hK : IsCompact K)
    (hKU : K ⊆ U) (k : ℕ) : ∃ B, 0 ≤ B ∧ ∀ y ∈ K, ‖iteratedFDeriv ℝ k f y‖ ≤ B := by
  have hcont : ContinuousOn (fun y => iteratedFDeriv ℝ k f y) U := fun y hy =>
    ((hf.contDiffAt (hU.mem_nhds hy)).continuousAt_iteratedFDeriv (by exact_mod_cast le_top)).continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hcont.mono hKU)
  exact ⟨max C 0, le_max_right _ _, fun y hy => (hC y hy).trans (le_max_left _ _)⟩
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
