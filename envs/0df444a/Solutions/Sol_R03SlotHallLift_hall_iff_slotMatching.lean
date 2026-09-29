-- Prove2me | solution 1 for R03SlotHallLift.hall_iff_slotMatching
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T11:13:54.854963+00:00
-- url     : https://prove2.me/submissions/774c8a65-2f49-4365-9367-026df4c61983

import Mathlib
import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_809c83f713_sp05_port_balanced_slot_factor_lift_formalizatio

namespace R03SlotHallLift

open CubicP3Partition

universe u

variable {V : Type u} [Fintype V]

noncomputable section
open scoped Classical

end
end R03SlotHallLift

open R03SlotHallLift
open CubicP3Partition
universe u
variable {V : Type u} [Fintype V]
open scoped Classical
theorem solution (R : V → Fin 2 → V → Prop) (C : Finset V) :
    HallCondition R C ↔ SlotMatching R C := by
  classical
  simpa [HallCondition, SlotMatching] using
    (Fintype.all_card_le_filter_rel_iff_exists_injective
      (fun s w => slotRel R C s w))
