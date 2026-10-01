-- Prove2me | solution 1 for burau_liftS_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T23:08:14.25486+00:00
-- url     : https://prove2.me/submissions/b3e80af2-13f8-4ea1-bfae-135f40ccf5a3

import Definitions.Def_burau_reduced_braid_group
import Definitions.Def_BurauFaithful_UnreducedBurau
import Theorems.Thm_burau_sLift_pow_four

set_option autoImplicit false

/-- `liftS ^ 4 = 1` in the reduced braid group `Q`. -/
theorem solution : BurauNC.liftS ^ 4 = 1 := by
  have h2 : BurauNC.liftS = BurauNC.q (BurauFaithful.sLift : BurauNC.B3) := rfl
  rw [h2, ← map_pow, burau_sLift_pow_four]
  exact (QuotientGroup.eq_one_iff (N := Subgroup.normalClosure ({BurauNC.Delta4} : Set BurauNC.B3))
      BurauNC.Delta4).mpr (Subgroup.subset_normalClosure (by simp))
