-- Prove2me | solution 1 for QPK.map_mulSwap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:49.944354+00:00
-- url     : https://prove2.me/submissions/4a7f2ff0-18ab-4805-b9ca-533fda9627d0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarMeasureUniqueness
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_SiegelMeasureDefinition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology Set
open scoped ENNReal Pointwise
open QPK
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace QPK
theorem _root_.solution (Q : Measure (G × G)) (g : G × G → G × G) (hg : MeasurePreserving g Q Q)
    (f : G → G) (hf : Measurable f) (h : ∀ p : G × G, f (p.2 * p.1) = (g p).2 * (g p).1) :
    (Q.map (fun p : G × G => p.2 * p.1)).map f = Q.map (fun p : G × G => p.2 * p.1) := by
  have hm : Measurable (fun p : G × G => p.2 * p.1) := measurable_snd.mul measurable_fst
  rw [Measure.map_map hf hm]
  have e : f ∘ (fun p : G × G => p.2 * p.1) = (fun p : G × G => p.2 * p.1) ∘ g := funext h
  rw [e, ← Measure.map_map hm hg.measurable, hg.map_eq]
end QPK
