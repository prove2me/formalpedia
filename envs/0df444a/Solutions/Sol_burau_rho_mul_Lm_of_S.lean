-- Prove2me | solution 1 for burau_rho_mul_Lm_of_S
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-10-01T06:28:50.788148+00:00
-- url     : https://prove2.me/submissions/68c87518-2470-460b-acdb-67b3ef44377b

import Definitions.Def_burau_cf_list
import Definitions.Def_burau_rho
import Definitions.Def_burau_srule_defs
import Theorems.Thm_burau_rho_T
import Theorems.Thm_burau_liftS_conj_zpow

set_option autoImplicit false

open BurauNC

theorem solution (X : BurauNC.M2) (k : ℤ) (hX : X.det = 1)
    (hS : BurauNC.rho (X * BurauNC.Sm) = BurauNC.rho X * BurauNC.liftS)
    (hk : BurauNC.rho ((X * BurauNC.Lm k) * BurauNC.Sm) =
      BurauNC.rho (X * BurauNC.Lm k) * BurauNC.liftS) :
    BurauNC.rho (X * BurauNC.Lm k) =
      BurauNC.rho X * BurauNC.liftS⁻¹ * BurauNC.liftT ^ (-k) * BurauNC.liftS := by

  have hdet : (X * Sm).det = 1 := by rw [Matrix.det_mul, hX, Sm_det_eq_one, mul_one]
  have hLm : Lm k * Sm = Sm * Tm (-k) := by
    simpa using (Sm_mul_Tm (-k)).symm
  have hmat : (X * Lm k) * Sm = (X * Sm) * Tm (-k) := by
    rw [mul_assoc, hLm, mul_assoc]
  have h1 : rho ((X * Lm k) * Sm) = rho X * liftS * liftT ^ (-k) := by
    rw [hmat, burau_rho_T (X * Sm) (-k) hdet, hS]
  rw [hk] at h1
  have h2 : rho (X * Lm k) = rho X * liftS * liftT ^ (-k) * liftS⁻¹ := by
    rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
  rw [h2]
  have h3 : rho X * liftS * liftT ^ (-k) * liftS⁻¹
          = rho X * (liftS * liftT ^ (-k) * liftS⁻¹) := by group
  rw [h3, burau_liftS_conj_zpow (-k)]
  group
