-- Prove2me | solution 1 for Yukon.MultiAnchor.exists_large_fiber_2104d33ae4e5
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-29T21:59:33.035796+00:00
-- url     : https://prove2.me/submissions/3442b2b9-ec36-4a6f-8bd4-91a2a0591480

import Mathlib
open scoped BigOperators
theorem solution {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (sieve : Nat)
    (hlarge : Fintype.card β * sieve < Fintype.card α) :
    ∃ y : β, sieve < (Finset.univ.filter fun x : α => f x = y).card := by
  classical
  by_contra! hall
  have hsum : Fintype.card α =
      ∑ y : β, (Finset.univ.filter fun x : α => f x = y).card := by
    rw [← Finset.card_univ]
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset α))
      (t := (Finset.univ : Finset β)) (f := f)
      (fun _ _ => Finset.mem_univ _))
  have hle : Fintype.card α ≤ Fintype.card β * sieve := by
    rw [hsum]
    calc
      (∑ y : β, (Finset.univ.filter fun x : α => f x = y).card) ≤
          ∑ _y : β, sieve := Finset.sum_le_sum fun y _ => hall y
      _ = Fintype.card β * sieve := by simp
  omega
