-- Prove2me | solution 1 for WilliamsonShmoys.partition_card_sum_of_disjoint_cover__p2m_9b39c159_5abf_402e_b341_b70b3524bea9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:33:31.89254+00:00
-- url     : https://prove2.me/submissions/a8d48e90-8ed0-4ba2-aaa2-1f88367a975b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open Finset

theorem solution {V : Type} [Fintype V] [LinearOrder V] (C : V → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hcover : Finset.univ.biUnion C = Finset.univ) :
    (∑ i : V, (C i).card) = Fintype.card V := by
  have hcard := Finset.card_biUnion (s := (Finset.univ : Finset V)) (t := C) ?_
  · rw [hcover] at hcard
    simpa using hcard.symm
  · intro i hi j hj hij
    exact hdisj i j hij