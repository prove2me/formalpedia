-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.keyRep_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:57:11.554572+00:00
-- url     : https://prove2.me/submissions/1080eb62-7466-48f3-966b-971975459bd2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_KeyDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepDefs
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_approx_pow_two
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped ComplexConjugate
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
private theorem le_two_pow_self (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
    rw [pow_succ]
    omega
end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (hS : KeyStart) (hN : KeyNewton) (hE : KeyExact) : KeyRep := by
  intro a b c d ha hd lam hlam hadm m _ _ Λ hsd hgen hi₁ hi₂ l hl x y hxy T i₀ hi₀ hT
  have h : KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀ :=
    ⟨hadm, hsd, hgen, hi₁, hi₂, hl, hxy, hi₀, hT⟩
  obtain ⟨w, hw⟩ := hS a b c d ha hd lam hlam m Λ l x y T i₀ h
  obtain ⟨K₀, hK⟩ := hE a b c d ha hd lam hlam m Λ l x y T i₀ h
  obtain ⟨w', hw'⟩ := approx_pow_two hN a b c d ha hd lam hlam m Λ l x y T i₀ h w hw K₀
  exact hK (2 ^ K₀) (le_two_pow_self K₀) w' hw'
end PI.UnitaryGroupMassFormula.UnimodLocStd
