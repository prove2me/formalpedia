-- Prove2me | solution 1 for WilliamsonShmoys.card_subtype_le_univ
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:50:18.370114+00:00
-- url     : https://prove2.me/submissions/6c4cf465-799a-4e90-93c5-45f495282c3e

import Mathlib

theorem solution
    {α : Type} [Fintype α] (p : α → Prop)
    [DecidablePred p] :
    Fintype.card {x // p x} ≤ Fintype.card α :=
  Fintype.card_subtype_le p
