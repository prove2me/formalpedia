-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.span_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:17:32.585061+00:00
-- url     : https://prove2.me/submissions/be0a1eeb-5824-41a4-9bb8-ac2065b09bac

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_ConjSubMulVec
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Pw_add
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Pw_smul
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Pw_zero
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Pw_e
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_fe
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_hJ_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
variable {n r : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ}
variable (hG : Gram ε e f)
include hG
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (k : ℕ) {v : Fin n → ℂ} (hv : v ∈ spanLt e k) :
    (∀ b : Fin r, k ≤ b.val → hJ ε (f b) v = 0) ∧ (∀ b, hJ ε (e b) v = 0) ∧ Pw ε e f v = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, hd, rfl⟩ := hx
    refine ⟨fun b hb => ?_, fun b => hG.ee b d, Pw_e hG d⟩
    rw [fe hG, if_neg]
    rintro rfl
    exact (not_lt.2 hb) hd
  | zero => exact ⟨fun b _ => hJ_zero ε _, fun b => hJ_zero ε _, Pw_zero⟩
  | add x y _ _ hx hy =>
    exact ⟨fun b hb => by rw [hJ_add, hx.1 b hb, hy.1 b hb, add_zero],
      fun b => by rw [hJ_add, hx.2.1 b, hy.2.1 b, add_zero], by rw [Pw_add, hx.2.2, hy.2.2, add_zero]⟩
  | smul c x _ hx =>
    exact ⟨fun b hb => by rw [hJ_smul, hx.1 b hb, mul_zero], fun b => by rw [hJ_smul, hx.2.1 b, mul_zero],
      by rw [Pw_smul, hx.2.2, smul_zero]⟩
end PI.NMeasInv.UnitaryGroupMassFormula
