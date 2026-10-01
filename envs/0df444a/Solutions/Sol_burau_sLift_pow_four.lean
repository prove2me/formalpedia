-- Prove2me | solution 1 for burau_sLift_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T22:57:37.987179+00:00
-- url     : https://prove2.me/submissions/106a532b-ca08-4c56-a78a-29db0bd604ef

import Definitions.Def_burau_reduced_braid_group
import Definitions.Def_BurauFaithful_UnreducedBurau
import Theorems.Thm_BurauFaithful_braid_three_amalgam_dictionary

set_option autoImplicit false

/-- `sLift ^ 4 = Δ⁴` in `B₃` (dictionary: `sLift² = uLift³ = (σ₀σ₁)³`). -/
theorem solution : (BurauFaithful.sLift : BurauNC.B3) ^ 4 = BurauNC.Delta4 := by
  have h : (BurauFaithful.sLift : BurauNC.B3) ^ 2 = (BurauNC.g0 * BurauNC.g1) ^ 3 :=
    BurauFaithful.braid_three_amalgam_dictionary.2.2.1
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h, BurauNC.Delta4, ← pow_mul]
