-- Prove2me | solution 1 for burau_rho_mul_Sm_of_L_rule
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:53:34.068601+00:00
-- url     : https://prove2.me/submissions/59fa629f-a2f4-4eec-a947-03368229fb17

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

theorem solution
    (hL : ∀ X : BurauNC.M2, X.det = 1 → ∀ k : ℤ,
      BurauNC.rho (X * BurauNC.Lm k) =
        BurauNC.rho X * BurauNC.liftS⁻¹ * BurauNC.liftT ^ (-k) * BurauNC.liftS) :
    ∀ M : BurauNC.M2, M.det = 1 →
      BurauNC.rho (M * BurauNC.Sm) = BurauNC.rho M * BurauNC.liftS := by
  intro M hd
  by_cases h0 : M 0 0 = 0
  · exact burau_rho_mul_Sm_terminal M hd h0
  · have hN : ((M * BurauNC.Tm (-(M 0 1 / M 0 0))) * BurauNC.Sm).det = 1 := by
      rw [Matrix.det_mul, Matrix.det_mul, hd, BurauNC.Sm_det_eq_one]
      simp [BurauNC.Tm, Matrix.det_fin_two]
    rw [BurauNC.mul_Sm_eq M, hL _ hN, BurauNC.EZ213.step M h0, neg_neg]
