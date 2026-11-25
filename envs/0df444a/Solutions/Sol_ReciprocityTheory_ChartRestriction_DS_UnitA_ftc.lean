-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitA.ftc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:14:52.491452+00:00
-- url     : https://prove2.me/submissions/d93a11b0-fbc7-4e66-9488-f098675508d0

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
namespace ReciprocityTheory.ChartRestriction.DS.UnitA
theorem _root_.solution {φ : ℝ → G} (hφc : Continuous φ) (hφ0 : φ 0 = 1) {a a' : G → ℂ} (ha' : Continuous a')
    (hd : ∀ x t, HasDerivAt (fun s => a (x * φ s)) (a' (x * φ t)) t) (x : G) (t : ℝ) :
    ∫ s in (0:ℝ)..t, a' (x * φ s) = a (x * φ t) - a x := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => a (x * φ s))
    (f' := fun s => a' (x * φ s)) (a := 0) (b := t) (fun s _ => hd x s)
    ((ha'.comp (continuous_const.mul hφc)).intervalIntegrable 0 t)
  simpa only [hφ0, mul_one] using h
end ReciprocityTheory.ChartRestriction.DS.UnitA
