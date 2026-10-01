-- Prove2me | solution 1 for burau_liftU_cube
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T22:45:31.461849+00:00
-- url     : https://prove2.me/submissions/f678bb26-38cd-4f92-92e4-c8b78a1f57eb

import Definitions.Def_burau_reduced_braid_group
import Definitions.Def_BurauFaithful_UnreducedBurau
import Theorems.Thm_BurauFaithful_braid_three_amalgam_dictionary

set_option autoImplicit false

/-- Coxeter relation `(liftT · liftS)^3 = liftS^2` in the reduced braid group. -/
theorem solution : (BurauNC.liftT * BurauNC.liftS) ^ 3 = BurauNC.liftS ^ 2 := by
  have q_g0 : BurauNC.q BurauNC.g0 = BurauNC.liftT⁻¹ := by
    show BurauNC.q BurauNC.g0 = (BurauNC.q BurauNC.g0⁻¹)⁻¹
    rw [map_inv, inv_inv]
  have q_uLift : BurauNC.q (BurauFaithful.uLift : BurauNC.B3)
      = BurauNC.liftT * BurauNC.liftS := by
    have h1 : (BurauFaithful.sLift : BurauNC.B3)
        = (BurauNC.g0 : BurauNC.B3) * (BurauFaithful.uLift : BurauNC.B3) :=
      BurauFaithful.braid_three_amalgam_dictionary.2.2.2
    have h' : BurauNC.q (BurauFaithful.sLift : BurauNC.B3)
        = BurauNC.liftT⁻¹ * BurauNC.q (BurauFaithful.uLift : BurauNC.B3) := by
      have h2 := congrArg BurauNC.q h1
      rw [map_mul, q_g0] at h2
      exact h2
    calc BurauNC.q (BurauFaithful.uLift : BurauNC.B3)
        = BurauNC.liftT * (BurauNC.liftT⁻¹ * BurauNC.q (BurauFaithful.uLift : BurauNC.B3)) := by
          group
      _ = BurauNC.liftT * BurauNC.liftS := by
          rw [← h', show BurauNC.q (BurauFaithful.sLift : BurauNC.B3) = BurauNC.liftS from rfl]
  have h1 : BurauNC.liftT * BurauNC.liftS = BurauNC.q (BurauFaithful.uLift : BurauNC.B3) :=
    q_uLift.symm
  have h2 : (BurauFaithful.uLift : BurauNC.B3) ^ 3 = (BurauFaithful.sLift : BurauNC.B3) ^ 2 :=
    BurauFaithful.braid_three_amalgam_dictionary.2.2.1.symm
  calc (BurauNC.liftT * BurauNC.liftS) ^ 3
      = BurauNC.q ((BurauFaithful.uLift : BurauNC.B3) ^ 3) := by rw [h1, ← map_pow]
    _ = BurauNC.q ((BurauFaithful.sLift : BurauNC.B3) ^ 2) := by rw [h2]
    _ = BurauNC.liftS ^ 2 := by
        rw [show BurauNC.q ((BurauFaithful.sLift : BurauNC.B3) ^ 2)
            = (BurauNC.q (BurauFaithful.sLift : BurauNC.B3)) ^ 2 from map_pow _ _ 2,
          show BurauNC.q (BurauFaithful.sLift : BurauNC.B3) = BurauNC.liftS from rfl]
