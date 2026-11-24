-- Prove2me | solution 1 for QPK.map_val_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:05:28.966336+00:00
-- url     : https://prove2.me/submissions/bbd34105-9139-488c-b02f-0f827f2c8ba4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarMeasureUniqueness

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology
open scoped ENNReal
open QPK
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace QPK
theorem _root_.solution (K' : Subgroup G) (g : K') (α : Measure K') :
    (α.map (fun x => g * x)).map Subtype.val = (α.map Subtype.val).map (fun x => (g : G) * x) := by
  have hv : Measurable (Subtype.val : K' → G) := measurable_subtype_coe
  have hm : Measurable (fun x : K' => g * x) := by
    have h : Measurable (fun x : K' => (g : G) * (x : G)) := (measurable_const_mul (g : G)).comp hv
    exact h.subtype_mk
  rw [Measure.map_map hv hm, Measure.map_map (measurable_const_mul _) hv]
  rfl
end QPK
