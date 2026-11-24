-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.KTy.card_filter_comp
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T05:19:39.250643+00:00
-- url     : https://prove2.me/submissions/8c9250b0-11a9-4629-ba1d-8acfe7eac33b

import Mathlib


theorem solution {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → Prop) [DecidablePred f] :
    (Finset.univ.filter fun a => f (e a)).card = (Finset.univ.filter f).card := by
  exact Finset.card_equiv e (by intro i; simp)
