-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitA.nrm_rt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:14.058532+00:00
-- url     : https://prove2.me/submissions/cb9bde4c-47b5-4b1c-813d-8b5f26c587b9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_UnitarizeA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.UnitA
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] (μ : Measure G)
variable {μ}
variable [μ.IsMulRightInvariant]
namespace ReciprocityTheory.ChartRestriction.DS.UnitA
theorem _root_.solution {a : G → ℂ} (ha : AEStronglyMeasurable a μ) (g : G) :
    nrm μ (fun x => a (x * g)) = nrm μ a := by
  unfold nrm
  have h := eLpNorm_comp_measurePreserving (p := 2) ha (measurePreserving_mul_right μ g)
  exact congrArg ENNReal.toReal h
end ReciprocityTheory.ChartRestriction.DS.UnitA
