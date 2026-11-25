-- Prove2me | solution 1 for PI.WGB.GoodB_X_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:45:15.084781+00:00
-- url     : https://prove2.me/submissions/ac9566ad-3ebb-4501-aa72-bd7271466c07

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB
import Theorems.Thm_PI_WGB_FiltB_mono
import Theorems.Thm_PI_WGB_X_mem_FiltB
import Theorems.Thm_PI_WGB_rowAct_X_B

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGB
theorem _root_.solution {n N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (hd : ∀ a, M a a = 1)
    (ho : ∀ a b, a ≠ b → M a b ≠ 0 → prowB n N a < prowB n N b) (v : Fin N × Fin N) :
    GoodB (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) M) (psiB n N) (X v) (psiB n N v) := by
  refine ⟨X_mem_FiltB _ v, ?_⟩
  rw [rowAct_X_B, ← Finset.add_sum_erase _ _ (Finset.mem_univ v.1), hd, map_one, one_mul, Prod.mk.eta,
    add_sub_cancel_left]
  refine Submodule.sum_mem _ fun b hb => ?_
  have hb' : b ≠ v.1 := Finset.ne_of_mem_erase hb
  by_cases h0 : M v.1 b = 0
  · rw [h0, map_zero, zero_mul]
    exact Submodule.zero_mem _
  · rw [← smul_eq_C_mul]
    refine Submodule.smul_mem _ _ (FiltB_mono _ ?_ (X_mem_FiltB _ (b, v.2)))
    exact ho v.1 b (Ne.symm hb') h0
end PI.WGB
