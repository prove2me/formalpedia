-- Prove2me | solution 1 for PI.Dv.GLP.coef_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:08:50.675875+00:00
-- url     : https://prove2.me/submissions/d5012086-3ea4-4ccc-b6a9-ab3b6b5c1883

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw
import Theorems.Thm_PI_Dv_GLP_asAlg_eS
import Theorems.Thm_PI_Dv_GLP_tau_eS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Representation
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.GLP
theorem _root_.solution [CharZero K] (T : GoodSet K G) (s t : T.S) (z : G) :
    ∑ x : G, cS T s x * cS T t (x⁻¹ * z) = if s = t then cS T s z else 0 := by
  have key : ∑ x : G, cS T s x * cS T t (x⁻¹ * z) =
      ((Module.finrank K (T.W t) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
        LinearMap.trace K _ (T.tau t z⁻¹ * (T.tau t).asAlgebraHom (eS T s)) := by
    rw [asAlg_eS, Finset.mul_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, ← map_mul]
    simp only [cS, mul_inv_rev, inv_inv]
    ring
  rw [key, tau_eS]
  split_ifs with h
  · subst h
    rw [mul_one, cS]
  · rw [mul_zero, map_zero, mul_zero]
end PI.Dv.GLP
