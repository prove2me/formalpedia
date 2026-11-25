-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_H_self_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:11:05.123896+00:00
-- url     : https://prove2.me/submissions/7962de21-874b-4433-a12d-4fc9736e870d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepArith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepHSelfInt
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_H_int
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_H_re


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
variable (m : Type) [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (hOK : CmOK a b c d) (Λ : AddSubgroup (m → ℂ))
    (hΛ : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ)
    {x : m → ℂ} (hx : x ∈ Λ) :
    ∃ n : ℤ, stdH (cmL a b d ha hd lam hlam) m x x = repKappa a b d ha hd lam hlam * n := by
  obtain ⟨n, c₂, h1, h2⟩ := rep_H_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hx hx
  have him : (stdH (cmL a b d ha hd lam hlam) m x x).im = 0 := by
    rw [← rep_H_re (cmL a b d ha hd lam hlam) m x]
    simp
  have hc : (c₂ : ℂ) = 0 := by
    have : (c₂ : ℝ) = 0 := by rw [← h2, him]
    exact_mod_cast this
  refine ⟨n, ?_⟩
  rw [h1, hc]
  ring
end PI.UnitaryGroupMassFormula.UnimodLocStd
