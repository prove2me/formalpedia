-- Prove2me | solution 1 for PI.HookSteps.hook_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:15:25.015904+00:00
-- url     : https://prove2.me/submissions/a39ab7c7-8ece-4d3c-881d-b385118fa916

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_HookNorm
import Theorems.Thm_PI_HookSteps_Pn_succ_shift
import Theorems.Thm_PI_HookSteps_Qn_succ_shift
import Theorems.Thm_PI_HookSteps_Pn_last_zero
import Theorems.Thm_PI_HookSteps_Qn_last_zero
import Theorems.Thm_PI_HookSteps_castSucc2_injective
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookSteps
namespace PI.HookSteps
theorem _root_.solution : HookNormOf := by
  intro hR hH hL hS
  suffices key : ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν →
      fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) * (Pn ν : ℚ) = (Qn ν : ℚ) by
    intro N ν hν
    have := key N ν hν
    unfold Pn Qn at this
    simp only [Nat.cast_prod] at this
    exact this
  intro N
  induction N with
  | zero => intro ν _; simp [Pn, Qn, hw, fockQ]
  | succ n ih =>
    suffices hk : ∀ (k : ℕ) (ν : Fin (n + 1) → ℕ), Antitone ν → ν (Fin.last n) = k →
        fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) * (Pn ν : ℚ) = (Qn ν : ℚ) by
      intro ν hν; exact hk _ ν hν rfl
    intro k
    induction k with
    | zero =>
      intro ν hν h0
      have hν' : Antitone (fun i : Fin n => ν i.castSucc) :=
        fun a b hab => hν (Fin.castSucc_le_castSucc_iff.2 hab)
      rw [hL n ν hν h0, hR _ _ _ (castSucc2_injective n), Pn_last_zero n ν h0, Qn_last_zero n ν h0,
        Nat.cast_mul, Nat.cast_mul, ← ih _ hν']
      ring
    | succ k ihk =>
      intro ν hν hk
      have hge : ∀ i, 1 ≤ ν i := fun i => by have := hν (Fin.le_last i); omega
      obtain ⟨μ, rfl⟩ : ∃ μ : Fin (n + 1) → ℕ, ν = fun i => μ i + 1 :=
        ⟨fun i => ν i - 1, funext fun i => by have := hge i; show ν i = ν i - 1 + 1; omega⟩
      have hμ : Antitone μ := fun a b hab => by have := hν hab; simp only at this; omega
      have hμk : μ (Fin.last n) = k := by simp only at hk; omega
      rw [Pn_succ_shift, Qn_succ_shift, hH _ μ hμ, hS _ μ hμ, Nat.cast_mul, Nat.cast_prod,
        ← ihk μ hμ hμk]
      ring
end PI.HookSteps
