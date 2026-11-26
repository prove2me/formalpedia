-- Prove2me | solution 1 for Sendov.eq_zero_of_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:06:37.036966+00:00
-- url     : https://prove2.me/submissions/edbc8356-09c2-41f9-91d2-a884bad2480e

import Definitions.Def_Sendov_Counterexample_Factor
import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Boundary

set_option autoImplicit false
open Sendov
open Polynomial
namespace Sendov
theorem _root_.solution {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x) (h : s.sum = 0) :
    ∀ x ∈ s, x = 0 := by
  intro x hx
  have hsplit : s.sum = x + (s.erase x).sum := by
    conv_lhs => rw [← Multiset.cons_erase hx]
    rw [Multiset.sum_cons]
  have hrest : 0 ≤ (s.erase x).sum :=
    Multiset.sum_nonneg fun y hy => hs y (Multiset.mem_of_mem_erase hy)
  rw [hsplit] at h
  have := hs x hx
  linarith
end Sendov
