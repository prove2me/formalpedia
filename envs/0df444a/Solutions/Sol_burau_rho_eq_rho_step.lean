-- Prove2me | solution 1 for burau_rho_eq_rho_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:53:43.73884+00:00
-- url     : https://prove2.me/submissions/5c4cb0ab-2e09-41b6-9772-3792d63b4117

import Definitions.Def_burau_cf_list
import Definitions.Def_burau_rho
import Definitions.Def_burau_srule_defs
import Definitions.Def_burau_srule_defs2
import Theorems.Thm_burau_rho_T
import Theorems.Thm_burau_liftS_conj_zpow
import Theorems.Thm_burau_rho_mul_Sm_terminal

set_option autoImplicit false

open BurauNC

namespace BurauNC.EZ213

theorem step (M : BurauNC.M2) (h0 : M 0 0 ≠ 0) :
    BurauNC.rho M =
      BurauNC.rho ((M * BurauNC.Tm (-(M 0 1 / M 0 0))) * BurauNC.Sm) *
        BurauNC.liftS⁻¹ * BurauNC.liftT ^ (M 0 1 / M 0 0) := by
  have hdec := BurauNC.euclid_decrease M h0
  obtain ⟨k, hk⟩ : ∃ k, (M 0 0).natAbs = k + 1 :=
    ⟨(M 0 0).natAbs - 1, by have := Int.natAbs_pos.mpr h0; omega⟩
  unfold BurauNC.rho
  rw [hk, BurauNC.rhoIter, if_neg h0, BurauNC.rhoIter_eq_rhoIter k _ (by omega)]

end BurauNC.EZ213

theorem solution (M : BurauNC.M2) (h0 : M 0 0 ≠ 0) :
    BurauNC.rho M =
      BurauNC.rho ((M * BurauNC.Tm (-(M 0 1 / M 0 0))) * BurauNC.Sm) *
        BurauNC.liftS⁻¹ * BurauNC.liftT ^ (M 0 1 / M 0 0) :=
  BurauNC.EZ213.step M h0
