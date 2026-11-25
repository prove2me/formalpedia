-- Prove2me | solution 1 for PositivityTheory.ThKCT.Unf.cont_M
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:59:10.139416+00:00
-- url     : https://prove2.me/submissions/74ace96a-e263-4e53-8098-22e2458f10a3

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_RightOfCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal NNReal Pointwise
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Unf
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (ν : Measure G) [ν.IsHaarMeasure] (m : Measure G) [SFinite m] {P : Set G} {K : Subgroup G}
omit [SFinite m]
namespace PositivityTheory.ThKCT.Unf
theorem _root_.solution [IsFiniteMeasureOnCompacts m] {f : G → ℝ} (hf : Continuous f) (hs : HasCompactSupport f) (h0 : 0 ≤ f) :
    Continuous fun g => ∫⁻ x, ENNReal.ofReal (f (x * g)) ∂m := by
  haveI : IsFiniteMeasureOnCompacts m.inv := ⟨fun C hC => by
    rw [Measure.inv_apply]; exact hC.inv.measure_lt_top⟩
  have h1 := continuous_integral_apply_inv_mul (μ := m.inv) hf hs
  have e : ∀ g, ∫⁻ x, ENNReal.ofReal (f (x * g)) ∂m = ENNReal.ofReal (∫ y, f (y⁻¹ * g) ∂m.inv) := fun g => by
    rw [Measure.inv, integral_map measurable_inv.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
    simp only [inv_inv]
    exact (ofReal_integral_eq_lintegral_ofReal (f := fun x => f (x * g)) (Continuous.integrable_of_hasCompactSupport
      (by fun_prop) (hs.comp_homeomorph (Homeomorph.mulRight g))) (ae_of_all _ fun x => h0 (x * g))).symm
  simp only [e]
  exact ENNReal.continuous_ofReal.comp h1
end PositivityTheory.ThKCT.Unf
