-- Prove2me | solution 1 for PI.ScPiFrameW.exists_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:19:51.188101+00:00
-- url     : https://prove2.me/submissions/4c5925b3-daec-4361-81cd-9d1aa3975d47

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_HJSumSmulRight
import Theorems.Thm_PI_ScPiFrameW_hJ_eq_sum
import Theorems.Thm_PI_ScPiFrameW_exists_rel
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScPiFrameW
open PI.ScPiExists
variable {n : ℕ}
namespace PI.ScPiFrameW
theorem _root_.solution (ε : Fin n → Bool) {ι : Type*} [Fintype ι] (u : ι → Fin n → ℂ)
    (h : Fintype.card ι < n) : ∃ y : Fin n → ℂ, y ≠ 0 ∧ ∀ i, hJ ε (u i) y = 0 := by
  obtain ⟨g, hg, j, hj⟩ := exists_rel (fun (j : Fin n) (i : ι) => star (u i j) * sg ε j)
    (by simpa using h)
  refine ⟨g, fun h0 => hj (congrFun h0 j), fun i => ?_⟩
  have := congrFun hg i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  rw [hJ_eq_sum, ← this]
  exact Finset.sum_congr rfl fun j _ => by ring
end PI.ScPiFrameW
