-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.PrescribedTop.pigeonhole
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-27T05:45:24.292071+00:00
-- url     : https://prove2.me/submissions/78b307cb-1846-426a-85a2-1c906e3f47dd

import Mathlib
import Init
/-!
# A prescribed-top-coefficient collision family below half radius

The included baseline attacks at radius `1/2` using the word `X^m` together with
*every* `m`-subset of the domain as an interpolation set.  This file generalises
that construction: it uses `t`-subsets with `t = m + r`, restricted to those whose
vanishing polynomial shares its top `r` coefficients with a fixed one.  Each such
subset still yields a genuine codeword agreeing with a single fixed word on all `t`
points, so the attack survives at radius `(n - t)/n = 1/2 - r/n`.

With `r = 8431` this certifies the unsafe suffix from grid index `122641` onward.
-/

namespace ProximityPrize.SubmissionUpper.PrescribedTop

open Polynomial
                                   
                             
open scoped NNReal


                             







































































/-- Pigeonhole over a `Fintype` codomain: some fibre beats the average.
`Finset.univ` on the codomain appears only inside this proof, where the codomain
is still a variable, so no giant instance is ever unfolded at a use site. -/
theorem _root_.solution {α β : Type} [Fintype β] [DecidableEq β]
    (s : Finset α) (f : α → β) (n : ℕ)
    (hn : Fintype.card β * n < s.card) :
    ∃ y : β, n < (s.filter (fun x => f x = y)).card := (by
  by_contra hcon
  push_neg at hcon
  have hsum : s.card
      = ∑ y ∈ (Finset.univ : Finset β), (s.filter (fun x => f x = y)).card :=
    Finset.card_eq_sum_card_fiberwise (fun a _ => Finset.mem_univ _)
  have hle : ∑ y ∈ (Finset.univ : Finset β), (s.filter (fun x => f x = y)).card
      ≤ ∑ _y ∈ (Finset.univ : Finset β), n :=
    Finset.sum_le_sum (fun y _ => hcon y)
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ] at hle
  omega
)
end PrescribedTop
end SubmissionUpper
end ProximityPrize
