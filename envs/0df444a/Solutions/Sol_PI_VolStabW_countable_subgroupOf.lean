-- Prove2me | solution 1 for PI.VolStabW.countable_subgroupOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:59:38.11061+00:00
-- url     : https://prove2.me/submissions/926c8053-b311-4952-9cdb-868656354629

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnfoldAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
namespace PI.VolStabW
theorem _root_.solution {Γ H : Subgroup G} [Countable Γ] :
    Countable ((Γ ⊓ H).subgroupOf H) := by
  refine Function.Injective.countable
    (f := fun x : (Γ ⊓ H).subgroupOf H =>
      (⟨((x : H) : G), (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 x.2)).1⟩ : Γ)) ?_
  intro a b hab
  have e : ((a : H) : G) = ((b : H) : G) := congrArg (fun z : Γ => (z : G)) hab
  exact Subtype.ext (Subtype.ext e)
end PI.VolStabW
