-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.approx_pow_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:48:49.175571+00:00
-- url     : https://prove2.me/submissions/46de9381-8897-4310-a5af-69a7cbc52b4d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_KeyDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepDefs

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
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (hN : KeyNewton) (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m) (h : KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀) (w : m → ℂ) (hw : ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ 1 w) :
    ∀ n : ℕ, ∃ w', ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ (2 ^ n) w' := by
  intro n
  induction n with
  | zero => exact ⟨w, by simpa using hw⟩
  | succ n ih =>
    obtain ⟨w₁, hw₁⟩ := ih
    have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
    obtain ⟨w₂, hw₂⟩ := hN a b c d ha hd lam hlam m Λ l x y T i₀ h (2 ^ n) (by omega) w₁ hw₁
    refine ⟨w₂, ?_⟩
    have he : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, mul_comm]
    rw [he]
    exact hw₂
end PI.UnitaryGroupMassFormula.UnimodLocStd
