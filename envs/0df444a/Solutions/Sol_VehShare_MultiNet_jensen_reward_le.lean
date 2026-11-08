-- Prove2me | solution 1 for VehShare.MultiNet.jensen_reward_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:39:03.27671+00:00
-- url     : https://prove2.me/submissions/348e3fb9-67b4-47dc-a08b-0d47cc2f1eb1

import Mathlib
import Definitions.Def_VehShare_MultiNet_reward
import Definitions.Def_VehShare_MultiNet_Rs

open VehShare.MultiNet in
theorem solution (P : VehShare.MultiNet.Instance) (K : ℕ) (q : VehShare.MultiNet.Policy P K)
    (π : VehShare.MultiNet.State P K → ℝ)
    (hπ0 : ∀ z, 0 ≤ π z) (hπ1 : ∑ z, π z = 1) :
    VehShare.MultiNet.reward q π ≤ VehShare.MultiNet.Rs P (fun i j => ∑ z, π z * q.1 z i j) := by
  unfold VehShare.MultiNet.reward VehShare.MultiNet.Rs
  have key : ∀ i j, ∑ z, π z * (q.1 z i j * P.I i j (q.1 z i j)) ≤
      (∑ z, π z * q.1 z i j) * P.I i j (∑ z, π z * q.1 z i j) := by
    intro i j
    have := (P.concave i j).le_map_sum (t := Finset.univ) (w := π) (p := fun z => q.1 z i j)
      (fun z _ => hπ0 z) hπ1 (fun z _ => ⟨(q.2.1 z i j).1, (q.2.1 z i j).2⟩)
    simpa only [smul_eq_mul] using this
  calc ∑ z, π z * ∑ i, ∑ j, P.Λ i j * q.1 z i j * P.I i j (q.1 z i j)
      = ∑ i, ∑ j, ∑ z, π z * (P.Λ i j * q.1 z i j * P.I i j (q.1 z i j)) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ i, ∑ j, P.Λ i j * ∑ z, π z * (q.1 z i j * P.I i j (q.1 z i j)) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun z _ => by ring)
    _ ≤ ∑ i, ∑ j, P.Λ i j * ((∑ z, π z * q.1 z i j) * P.I i j (∑ z, π z * q.1 z i j)) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (key i j) (P.Λ_nonneg i j)))
    _ = ∑ i, ∑ j, P.Λ i j * (∑ z, π z * q.1 z i j) * P.I i j (∑ z, π z * q.1 z i j) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        ring
