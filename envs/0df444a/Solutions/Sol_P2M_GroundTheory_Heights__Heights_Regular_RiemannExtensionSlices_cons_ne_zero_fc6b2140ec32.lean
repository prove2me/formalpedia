-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_cons_ne_zero_fc6b2140ec32
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:28.65793+00:00
-- url     : https://prove2.me/submissions/73c2bc66-4716-457c-ba1c-cd25deb11d8e

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
namespace GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
theorem _root_.solution {n : ℕ} {x : ℂ} (hx : x ≠ 0) {y : Fin n → ℂ} (hy : ∀ i, y i ≠ 0) :
    ∀ i, (Fin.cons x y : Fin (n + 1) → ℂ) i ≠ 0 := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hx
  · simpa using hy j
end GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
