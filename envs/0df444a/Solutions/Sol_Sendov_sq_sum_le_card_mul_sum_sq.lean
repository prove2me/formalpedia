-- Prove2me | solution 1 for Sendov.sq_sum_le_card_mul_sum_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:03:40.056897+00:00
-- url     : https://prove2.me/submissions/ff5973bf-6178-40ae-b2cd-3034d4a378ac

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (s : Multiset ℝ) (hs : ∀ b ∈ s, 0 ≤ b) :
    (s.sum) ^ 2 ≤ (s.card : ℝ) * (s.map (fun b => b ^ 2)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b t ih =>
    have hb := hs b (Multiset.mem_cons_self b t)
    have ht : ∀ u ∈ t, 0 ≤ u := fun u hu => hs u (Multiset.mem_cons_of_mem hu)
    rcases eq_or_ne t 0 with rfl | ht0
    · simp
    · have hIH := ih ht
      have hcard : (0 : ℝ) < (t.card : ℕ) := by
        have := Multiset.card_pos.2 ht0
        exact_mod_cast this
      have hsum : 0 ≤ t.sum := Multiset.sum_nonneg ht
      have hQ : (0 : ℝ) ≤ (t.map (fun b => b ^ 2)).sum :=
        Multiset.sum_nonneg (by
          intro y hy
          obtain ⟨u, _, rfl⟩ := Multiset.mem_map.1 hy
          exact sq_nonneg u)
      simp only [Multiset.sum_cons, Multiset.card_cons, Multiset.map_cons]
      push_cast
      nlinarith [hIH, sq_nonneg (t.sum - (t.card : ℝ) * b), hcard, hsum, hb, hQ]
end Sendov
