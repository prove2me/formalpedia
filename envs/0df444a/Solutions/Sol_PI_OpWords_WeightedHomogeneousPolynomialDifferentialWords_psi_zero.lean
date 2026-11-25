-- Prove2me | solution 1 for PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.psi_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:00:53.299798+00:00
-- url     : https://prove2.me/submissions/d2f27039-fd7c-4525-b4f4-e2e72e5f2797

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_IsWeightedHomogeneousPairingLeft
import Theorems.Thm_P2M_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_eval_aeval__0ef3796c825b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
theorem _root_.solution (i0 : Fin k) (f : Pol K k)
    (hv : ∀ p : Fin k ⊕ Fin k → K, ∑ i, p (Sum.inl i) * p (Sum.inr i) = 0 → eval p f = 0) :
    aeval (psiF K i0) f = 0 := by
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  apply MvPolynomial.funext
  intro p
  rw [eval_aeval', map_zero]
  apply hv
  have key : ∀ i, eval p (psiF K i0 (Sum.inr i)) =
      if i = i0 then -(∑ j ∈ Finset.univ.erase i0, p (Sum.inl j) * p (Sum.inr j))
      else p (Sum.inl i0) * p (Sum.inr i) := by
    intro i
    by_cases h : i = i0
    · subst h
      simp [psiF, tp]
    · simp [psiF, h]
  have key2 : ∀ i, eval p (psiF K i0 (Sum.inl i)) = p (Sum.inl i) := by
    intro i
    simp [psiF]
  simp only [key, key2]
  have h3 : ∑ i ∈ Finset.univ.erase i0, p (Sum.inl i) *
      (if i = i0 then -(∑ j ∈ Finset.univ.erase i0, p (Sum.inl j) * p (Sum.inr j))
        else p (Sum.inl i0) * p (Sum.inr i))
      = p (Sum.inl i0) * ∑ j ∈ Finset.univ.erase i0, p (Sum.inl j) * p (Sum.inr j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_neg (Finset.ne_of_mem_erase hi)]
    ring
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), h3, if_pos rfl]
  ring
end PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
