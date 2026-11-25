-- Prove2me | solution 1 for PI.Dv.GLP.eS_mul_eS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:15:25.16717+00:00
-- url     : https://prove2.me/submissions/c5a3e61f-4f58-43c7-aba3-168b8424ab10

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw
import Theorems.Thm_PI_Dv_GLP_eS_eq
import Theorems.Thm_PI_Dv_GLP_coef_mul

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
theorem _root_.solution [CharZero K] (T : GoodSet K G) (s t : T.S) :
    eS T s * eS T t = if s = t then eS T s else 0 := by
  have h1 : eS T s * eS T t =
      ∑ z : G, (∑ x : G, cS T s x * cS T t (x⁻¹ * z)) • MonoidAlgebra.of K G z := by
    rw [eS_eq, eS_eq, Finset.sum_mul_sum]
    simp only [smul_mul_smul_comm, ← map_mul]
    simp_rw [Finset.sum_smul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact Fintype.sum_equiv (Equiv.mulLeft x) _ _ (fun y => by simp)
  rw [h1]
  simp_rw [coef_mul]
  split_ifs with h
  · rw [eS_eq]
  · simp
end PI.Dv.GLP
