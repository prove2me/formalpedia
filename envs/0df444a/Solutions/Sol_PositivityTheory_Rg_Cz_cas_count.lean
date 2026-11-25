-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.cas_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:52:07.687185+00:00
-- url     : https://prove2.me/submissions/8edf194e-aa6a-416f-8915-0a1f2f597586

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_CountSame
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_CountCross
import Theorems.Thm_PositivityTheory_Rg_Cz_count_cross
import Theorems.Thm_PositivityTheory_Rg_Cz_count_eqb
import Theorems.Thm_PositivityTheory_Rg_Cz_count_rhs
import Theorems.Thm_PositivityTheory_Rg_Cz_count_same
import Theorems.Thm_PositivityTheory_Rg_Cz_count_up


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q] {C : Type} [DecidableEq C] {col : Q → C}
  {b : Q → Fin n} {S : Finset Q}
namespace PositivityTheory.Rg.Cz
theorem _root_.solution (hT : IsTab col b) (hS : ∀ p q, col p = col q → (p ∈ S ↔ q ∈ S))
    (R : Q → Q → ℝ) (N : ℝ) (hsymm : ∀ p q, R p q = R q p)
    (hsame : ∀ p q, col p = col q → p ≠ q → R p q = -N)
    (hcross : ∀ p ∈ S, ∀ c, c ≠ col p → ∑ q ∈ S.filter (fun q => col q = c), R p q ≤ N) :
    ((n * S.card : ℕ) : ℝ) * N + ∑ p ∈ S, ∑ q ∈ S.erase p, R p q ≤
      (∑ i : Fin n, ((S.filter fun p => b p = i).card : ℝ) *
        (((S.filter fun p => b p = i).card : ℝ) + 2 * (i : ℕ) + 1 - n)) * N := by
  rw [count_rhs, Finset.sum_mul]
  have hsplit : ∀ p, ∑ q ∈ S.erase p, R p q =
      (∑ q ∈ S, (if col q = col p ∧ q ≠ p then (1:ℝ) else 0)) * (-N) +
        ∑ q ∈ S, (if col q ≠ col p then R p q else 0) := by
    intro p
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    rw [← Finset.filter_ne' S p, Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : q = p
    · subst hq
      simp
    · by_cases hc : col q = col p
      · simp [hq, hc, hsame p q hc.symm (Ne.symm hq)]
      · simp [hq, hc]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, count_same hT]
  have hup : ∑ p ∈ S, ∑ q ∈ S, (if col q = col p ∧ b p < b q then (1:ℝ) else 0) =
      ∑ p ∈ S, ((n:ℝ) - 1 - (b p : ℕ)) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.sum_boole]
    exact count_up hT hS p hp
  have heq : ∑ p ∈ S, ∑ q ∈ S, (if col q ≠ col p ∧ b q = b p then N else 0) =
      ∑ p ∈ S, (((S.filter fun q => b q = b p).card : ℝ) - 1) * N := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [count_eqb hT p hp, add_sub_cancel_left, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> simp
  have hc := count_cross hT hS R N hsymm hcross
  rw [heq] at hc
  rw [hup]
  have hcard : ((n * S.card : ℕ) : ℝ) = ∑ p ∈ S, (n : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    push_cast
    ring
  rw [hcard]
  have e3 : ∑ p ∈ S, (((S.filter fun q => b q = b p).card : ℝ) + 2 * (b p : ℕ) + 1 - n) * N =
      (∑ p ∈ S, (n:ℝ)) * N + (2 * ∑ p ∈ S, ((n:ℝ) - 1 - (b p : ℕ))) * (-N) +
        ∑ p ∈ S, (((S.filter fun q => b q = b p).card : ℝ) - 1) * N := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [e3]
  linarith
end PositivityTheory.Rg.Cz
