-- Prove2me | solution 1 for SatiationFisherNSW.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:50:39.674101+00:00
-- url     : https://prove2.me/submissions/15e0bdfa-e4c0-4447-b1d9-8c6cd4612533

import Mathlib
import Definitions.Def_SatiationFisherNSW_NSWInstance
open scoped Classical

open SatiationFisherNSW in
theorem solution {B G : Type*} [Fintype B] [Fintype G] (I : SatiationFisherNSW.NSWInstance B G)
    (S : G → Option B) (i : B) :
    min (I.c i) (∑ j ∈ Finset.univ.filter (fun j => S j = some i), min (I.v i j) (I.c i)) =
      I.val i S := by
  unfold SatiationFisherNSW.NSWInstance.val
  by_cases h : ∃ j ∈ Finset.univ.filter (fun j => S j = some i), I.c i ≤ I.v i j
  · obtain ⟨j, hj, hcj⟩ := h
    have h1 : I.c i ≤ ∑ j ∈ Finset.univ.filter (fun j => S j = some i), min (I.v i j) (I.c i) :=
      (min_eq_right hcj).symm.le.trans
        (Finset.single_le_sum (f := fun j => min (I.v i j) (I.c i))
          (fun k _ => le_min (I.v_nonneg i k) (I.c_pos i).le) hj)
    have h2 : I.c i ≤ ∑ j ∈ Finset.univ.filter (fun j => S j = some i), I.v i j :=
      hcj.trans (Finset.single_le_sum (f := fun j => I.v i j) (fun k _ => I.v_nonneg i k) hj)
    rw [min_eq_left h1, min_eq_left h2]
  · push_neg at h
    congr 1
    exact Finset.sum_congr rfl (fun j hj => min_eq_left (h j hj).le)
