-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_maDensity_eq_zero_of_eventually_4e0ac8d1e147
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:54:32.740077+00:00
-- url     : https://prove2.me/submissions/1d07030d-56df-452c-94cf-d0fa2e6586d3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Weights
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_LineMu

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexConjugate
variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])
variable {II hII}
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
theorem _root_.solution {φ : Fin 1 → (Fin 1 → ℂ) → ℝ} {y : Fin 1 → ℂ}
    (h : ∀ j, φ j =ᶠ[nhds y] fun _ => 0) : maDensity φ y = 0 := by
  have hH : ∀ j, cxHessian (φ j) y = 0 := by
    intro j
    have h2 : fderiv ℝ (fderiv ℝ (φ j)) y = fderiv ℝ (fderiv ℝ (fun _ : Fin 1 → ℂ => (0 : ℝ))) y :=
      (h j).fderiv.fderiv_eq
    ext a b
    simp [cxHessian, h2]
  simp [maDensity, mixedDisc, hH]
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
