-- Prove2me | solution 1 for PI.VolStabSW.countable_subgroupOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:21:39.71441+00:00
-- url     : https://prove2.me/submissions/22c1f1fe-7c8c-4a63-87ab-b8380b9a2fa4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnfoldAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
namespace PI.VolStabSW
theorem _root_.solution {Γ H : Subgroup G} [Countable Γ] :
    Countable ((Γ ⊓ H).subgroupOf H) := by
  refine Function.Injective.countable (f := fun x : (Γ ⊓ H).subgroupOf H =>
    (⟨((x : H) : G), (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp x.2)).1⟩ : Γ)) ?_
  intro a b hab
  simp only [Subtype.mk.injEq] at hab
  exact Subtype.ext (Subtype.ext hab)
end PI.VolStabSW
