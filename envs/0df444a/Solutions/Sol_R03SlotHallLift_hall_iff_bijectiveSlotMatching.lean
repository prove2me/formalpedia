-- Prove2me | solution 1 for R03SlotHallLift.hall_iff_bijectiveSlotMatching
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T11:13:53.691603+00:00
-- url     : https://prove2.me/submissions/3667599f-bfc1-4777-acd1-ec048d515fc6

import Mathlib
import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_809c83f713_sp05_port_balanced_slot_factor_lift_formalizatio

namespace R03SlotHallLift

open CubicP3Partition

universe u

variable {V : Type u} [Fintype V]

noncomputable section
open scoped Classical

theorem hall_iff_slotMatching (R : V → Fin 2 → V → Prop) (C : Finset V) :
    HallCondition R C ↔ SlotMatching R C := by
  classical
  simpa [HallCondition, SlotMatching] using
    (Fintype.all_card_le_filter_rel_iff_exists_injective
      (fun s w => slotRel R C s w))


end
end R03SlotHallLift

open R03SlotHallLift
open CubicP3Partition
universe u
variable {V : Type u} [Fintype V]
open scoped Classical
theorem solution
    (R : V → Fin 2 → V → Prop) (C : Finset V)
    (hcard : Fintype.card (Slot C) = Fintype.card (Leaf C)) :
    HallCondition R C ↔ BijectiveSlotMatching R C := by
  constructor
  · intro h
    obtain ⟨f, hf_inj, hf_rel⟩ := (hall_iff_slotMatching R C).mp h
    refine ⟨f, ?_, hf_rel⟩
    exact (Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, hcard⟩
  · rintro ⟨f, hf_bij, hf_rel⟩
    apply (hall_iff_slotMatching R C).mpr
    exact ⟨f, hf_bij.1, hf_rel⟩
