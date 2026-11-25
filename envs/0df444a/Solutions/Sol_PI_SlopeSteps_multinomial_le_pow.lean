-- Prove2me | solution 1 for PI.SlopeSteps.multinomial_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:55.686513+00:00
-- url     : https://prove2.me/submissions/6ff560f1-5906-4256-900f-9ab571a698db

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_MonomialFactorizationLower
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
open PI PI.SlopeSteps
open Finset
namespace PI.SlopeSteps
theorem _root_.solution {N : ℕ} (f : Fin N → ℕ) : Nat.multinomial univ f ≤ N ^ (∑ a, f a) := by
  have h := Finset.sum_pow_eq_sum_piAntidiag (R := ℕ) (univ : Finset (Fin N)) (fun _ => (1 : ℕ)) (∑ a, f a)
  simp only [one_pow, prod_const_one, mul_one, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h
  rw [h]
  exact Finset.single_le_sum (f := fun k => Nat.multinomial univ k) (fun _ _ => Nat.zero_le _)
    (mem_piAntidiag.mpr ⟨rfl, fun i _ => mem_univ i⟩)
end PI.SlopeSteps
