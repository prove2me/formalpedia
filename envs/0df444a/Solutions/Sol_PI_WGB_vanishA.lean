-- Prove2me | solution 1 for PI.WGB.vanishA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:38.292315+00:00
-- url     : https://prove2.me/submissions/7da26737-6592-4eb3-aaaa-fdf604916d58

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_StepACleared
import Theorems.Thm_PI_WGB_elimA_inv
import Theorems.Thm_PI_WGB_elimA_cleared
import Theorems.Thm_Formalism_GradedWeylDivisibility_eval_idPoint_lpMinor
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
noncomputable section
open PI PI.WGB
open Formalism.GradedWeylDivisibility MvPolynomial
variable {n : ℕ}
namespace PI.WGB
theorem _root_.solution (g : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hR : RInvA (fun x => eval x g)) (hC : lhwline_CInv (fun x => eval x g))
    (hD : ∀ D : Fin (n + 1) × Fin (n + 1) → ℂ,
      (∀ a j : Fin (n + 1), a.val < n → a ≠ j → D (a, j) = 0) → eval D g = 0) :
    g = 0 := by
  set P : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ := ∏ s : Fin n,
    lpMinor ℂ (s.val + 1) (by have := s.isLt; omega) (by have := s.isLt; omega) with hPdef
  have hP : P ≠ 0 := by
    intro h
    have := congrArg (eval (idPoint ℂ (n + 1) (n + 1))) h
    simp only [hPdef, map_prod, eval_idPoint_lpMinor, Finset.prod_const_one, map_zero] at this
    exact one_ne_zero this
  have hgP : g * P = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hx : ∀ (s : ℕ) (hs : s + 1 ≤ n), eval x (lpMinor ℂ (s + 1) (by omega) (by omega) :
        MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) ≠ 0
    · have h1 : eval x g = eval (elimA n x) g :=
        (elimA_inv (fun y => eval y g) hR hC n x).symm
      rw [h1, hD _ (fun a j ha h => elimA_cleared x hx n le_rfl a j ha
        (fun e => h (Fin.ext e)) (Or.inl ha)), zero_mul]
    · push Not at hx
      obtain ⟨s, hs, hs0⟩ := hx
      have : eval x P = 0 := by
        rw [hPdef, map_prod]
        exact Finset.prod_eq_zero (i := ⟨s, by omega⟩) (Finset.mem_univ _) hs0
      rw [this, mul_zero]
  rcases mul_eq_zero.mp hgP with h | h
  · exact h
  · exact absurd h hP
end PI.WGB
