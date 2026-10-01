-- Prove2me | solution 1 for burau_liftS_sq_central
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T22:59:05.461883+00:00
-- url     : https://prove2.me/submissions/53e9ee35-8be4-4707-a622-5593a53275ed

import Definitions.Def_burau_reduced_braid_group
import Definitions.Def_BurauFaithful_UnreducedBurau
import Theorems.Thm_BurauFaithful_braid_three_amalgam_dictionary
import Theorems.Thm_BurauFaithful_braid_three_fullTwist_central

set_option autoImplicit false

/-- `liftS ^ 2` is central in `Q` (its preimage is the square of the Garside element). -/
theorem solution : BurauNC.liftS ^ 2 ∈ Subgroup.center BurauNC.Q := by
  have h2 : BurauNC.liftS ^ 2 = BurauNC.q ((BurauFaithful.sLift : BurauNC.B3) ^ 2) := by
    rw [show BurauNC.liftS = BurauNC.q (BurauFaithful.sLift : BurauNC.B3) from rfl, ← map_pow]
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (Subgroup.normalClosure ({BurauNC.Delta4} : Set BurauNC.B3)) y
  change BurauNC.q x * BurauNC.q ((BurauFaithful.sLift : BurauNC.B3) ^ 2)
      = BurauNC.q ((BurauFaithful.sLift : BurauNC.B3) ^ 2) * BurauNC.q x
  rw [← map_mul, ← map_mul]
  rw [show (BurauFaithful.sLift : BurauNC.B3) ^ 2 = (BurauNC.g0 * BurauNC.g1) ^ 3 from
    BurauFaithful.braid_three_amalgam_dictionary.2.2.1]
  exact congrArg BurauNC.q
    (Subgroup.mem_center_iff.mp BurauFaithful.braid_three_fullTwist_central x)
