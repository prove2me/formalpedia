-- Prove2me | solution 1 for WilliamsonShmoys.component_arithmetic_small__p2m_f8118d4e_7433_432b_871f_3e593ed76035_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:19:15.700201+00:00
-- url     : https://prove2.me/submissions/153a41c7-c7c1-44e0-9ee6-276d25e69056

import Mathlib
set_option autoImplicit false

theorem solution
    (n E : Nat)
    (parts : List (Prod Nat Nat))
    (hvertices : (parts.map Prod.fst).sum = n)
    (hedges : (parts.map Prod.snd).sum = E)
    (hparts : forall p, List.Mem p parts ->
      (3 <= p.1 -> p.2 <= 3 * p.1 - 6) /\
      (p.1 < 3 -> p.2 <= p.1))
    (hcard : 3 <= n)
    (hsmall : forall p, List.Mem p parts -> p.1 < 3) :
    E <= 3 * n - 6 := by
  have hpoint : forall p, List.Mem p parts -> p.2 <= p.1 := by
    intro p hp
    exact (hparts p hp).2 (hsmall p hp)
  have helper : forall l : List (Prod Nat Nat),
      (forall p, List.Mem p l -> p.2 <= p.1) ->
      (l.map Prod.snd).sum <= (l.map Prod.fst).sum := by
    intro l
    induction l with
    | nil =>
        intro hl
        exact Nat.le_refl 0
    | cons a l ih =>
        intro hl
        change a.2 + (l.map Prod.snd).sum <=
          a.1 + (l.map Prod.fst).sum
        exact Nat.add_le_add (hl a (List.Mem.head l))
          (ih (fun p hp => hl p (List.Mem.tail a hp)))
  have hsum : (parts.map Prod.snd).sum <= (parts.map Prod.fst).sum :=
    helper parts hpoint
  rw [hedges, hvertices] at hsum
  omega
