-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.ae_eq_eqOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:30:35.816644+00:00
-- url     : https://prove2.me/submissions/2c7ed7cd-27fd-4875-90fe-9ae39915dd7c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegGlue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {n : ℕ} {Ω : Set (V n)} {U U' : V n → ℂ} (hΩ : IsOpen Ω)
    (hU : ContinuousOn U Ω) (hU' : ContinuousOn U' Ω) (h : U =ᵐ[volume.restrict Ω] U') :
    EqOn U U' Ω := by
  exact Measure.eqOn_open_of_ae_eq h hΩ hU hU'
end ReciprocityTheory.L2DbarEstimates.C
