-- Prove2me | solution 1 for PandoraComb.observation_5
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:38:13.578898+00:00
-- url     : https://prove2.me/submissions/746c26bc-5973-461f-a203-778cc9b9e4ee

import Definitions.Def_PandoraComb_ClosedForms

namespace PandoraComb.Obs5Aux
open PandoraComb

theorem qL_cons {ι : Type*} (p : ι → ℝ) (a : ι) (l : List ι) :
    qL p (a :: l) = (1 - p a) * qL p l := by simp [qL]

theorem tele {ι : Type*} (p : ι → ℝ) :
    ∀ l : List ι, pL p l = ∑ j : Fin l.length, qL p (l.take j) * p (l.get j)
  | [] => by simp [pL, qL]
  | a :: l => by
    have ih := tele p l
    show pL p (a :: l) = ∑ j : Fin (l.length + 1), qL p ((a :: l).take j) * p ((a :: l).get j)
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.take_zero, Fin.val_succ, List.take_succ_cons]
    have e : ∀ j : Fin l.length, qL p (a :: l.take j) * p ((a :: l).get j.succ)
        = (1 - p a) * (qL p (l.take j) * p (l.get j)) := by
      intro j; rw [qL_cons]; simp; ring
    simp only [e, ← Finset.mul_sum, ← ih]
    simp [pL, qL]; ring

end PandoraComb.Obs5Aux

open PandoraComb PandoraComb.Obs5Aux in
theorem solution {ι : Type*} [DecidableEq ι] (p : ι → ℝ) (l : List ι) (hl : l.Nodup)
    (A B : Finset ι) (hAB : Disjoint A B) (hcover : A ∪ B = l.toFinset) :
    pL p l = pD p l A + pD p l B := by
  rw [tele, pD, pD, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hmem : l.get j ∈ A ∪ B := by rw [hcover]; simp [List.get_mem]
  simp only [List.get_eq_getElem] at hmem ⊢
  rcases Finset.mem_union.1 hmem with h | h
  · have hB : l[(j : ℕ)] ∉ B := Finset.disjoint_left.1 hAB h
    rw [if_pos h, if_neg hB, add_zero]
  · have hA : l[(j : ℕ)] ∉ A := fun h' => Finset.disjoint_left.1 hAB h' h
    rw [if_pos h, if_neg hA, zero_add]
