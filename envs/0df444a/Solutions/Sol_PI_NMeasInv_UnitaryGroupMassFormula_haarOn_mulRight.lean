-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.haarOn_mulRight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:57:28.190227+00:00
-- url     : https://prove2.me/submissions/7e3e6ffd-2533-44be-bdb1-6d1c9f2bedee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_RightInvOfContract
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_haarOn_map

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
open scoped ENNReal NNReal
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
attribute [local instance] Classical.propDecidable
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (N : Subgroup G) (hN : IsClosed (N : Set G)) {μ : Measure G} (hμ : HaarOn N μ)
    {n : G} (hn : n ∈ N) : HaarOn N (μ.map (fun x => x * n)) := haarOn_map N hN hμ (fun x => x * n) (Homeomorph.mulRight n) (by ext x; simp)
    (fun x hx => N.mul_mem hx hn) (fun s hs => ⟨s, hs, fun x => (mul_assoc s x n).symm⟩)
end PI.NMeasInv.UnitaryGroupMassFormula
