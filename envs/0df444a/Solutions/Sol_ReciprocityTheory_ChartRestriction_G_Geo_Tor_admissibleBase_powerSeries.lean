-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.admissibleBase_powerSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:29:44.888794+00:00
-- url     : https://prove2.me/submissions/e3525f79-fb2b-4e60-8e21-bcea54bc47cf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabMapCubical
import Definitions.Def_ReciprocityTheory_AdicCompleteness_IsAdicCompleteComapConstantCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
import Theorems.Thm_ReciprocityTheory_P1_isAdicComplete_ps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (k : Type) [Field k] : Out.AdmBase (PowerSeries k) (Ideal.span {PowerSeries.X}) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  have : IsAdicComplete (IsLocalRing.maximalIdeal k) k := by
    rw [IsLocalRing.maximalIdeal_eq_bot]; infer_instance
  have h := ReciprocityTheory.P1.isAdicComplete_ps (R := k)
  rwa [PowerSeries.maximalIdeal_eq_span_X] at h
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
