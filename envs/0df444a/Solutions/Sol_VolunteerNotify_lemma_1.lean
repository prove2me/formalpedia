-- Prove2me | solution 1 for VolunteerNotify.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:05:04.017449+00:00
-- url     : https://prove2.me/submissions/f73865a0-79bd-4cd5-b7ea-566f0355b44e

import Mathlib
import Definitions.Def_VolunteerNotify_f

open VolunteerNotify in
theorem solution {V S T : ℕ} (I : VolunteerNotify.Instance V S T) (x : VolunteerNotify.Decision V S T)
    (hx : ∀ v s t, x v s t ∈ Set.Icc (0 : ℝ) 1) : VolunteerNotify.f I x = ∑ v, VolunteerNotify.fv I x v := by
  unfold VolunteerNotify.f VolunteerNotify.fv
  have key : ∀ (t : Fin T) (s : Fin S), I.lam s t * (1 - ∏ v, (1 - x v s t * I.p v s)) =
      ∑ v, I.lam s t * (∏ u ∈ Finset.Iio v, (1 - I.p u s * x u s t)) * I.p v s * x v s t := by
    intro t s
    rw [Finset.prod_one_sub_ordered]
    rw [show ∀ S : ℝ, (1:ℝ) - (1 - S) = S from fun S => by ring]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have hI : (Finset.univ.filter (fun u => u < v)) = Finset.Iio v := by
      ext u; simp
    rw [hI]
    have hp : ∏ u ∈ Finset.Iio v, (1 - x u s t * I.p u s) =
        ∏ u ∈ Finset.Iio v, (1 - I.p u s * x u s t) :=
      Finset.prod_congr rfl (fun u _ => by ring)
    rw [hp]
    ring
  simp_rw [key]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  exact Finset.sum_comm
