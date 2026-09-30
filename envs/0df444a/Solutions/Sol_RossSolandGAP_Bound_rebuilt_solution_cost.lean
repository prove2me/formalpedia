-- Prove2me | solution 1 for RossSolandGAP.Bound.rebuilt_solution_cost
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:06:20.743271+00:00
-- url     : https://prove2.me/submissions/95c43ed9-5026-4dde-97a3-01059e21f797

import Definitions.Def_RossSolandGAP_Bound_Model
import Theorems.Thm_RossSolandGAP_Bound_knapsackBound_eq_lagrangean_bound
import Mathlib.Tactic
set_option autoImplicit false
open Finset RossSolandGAP.Bound

private theorem partition_sum {m n : ℕ} (a : Fin n → Fin m) (I : Finset (Fin m))
    (f : Fin m → Fin n → ℝ) :
    ∑ i ∈ I, ∑ j ∈ Jset a i, f i j = ∑ j, if a j∈I then f (a j) j else 0 := by
  classical
  simp only [Jset,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp

theorem solution {m n : ℕ} (hm : 1 < m) (c r : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (hb : ∀ i, 0 < b i) (hr : ∀ i j, 0 ≤ r i j)
    (a : Fin n → Fin m) (ha : IsCheapest c a) (ystar : Fin m → Fin n → ℝ)
    (hystar : ∀ i ∈ Iprime r b a, IsOptPK hm c r b a i (ystar i))
    (k : Fin n → Fin m) (hk : ∀ j, k j ≠ a j ∧ pen hm c a j = c (k j) j - c (a j) j) :
    FeasiblePR (rebuilt r b a ystar k) ∧
    cost c (rebuilt r b a ystar k) = LB hm c r b a ystar ∧
    (FeasibleP r b (rebuilt r b a ystar k) →
      ∀ x, FeasibleP r b x → cost c (rebuilt r b a ystar k) ≤ cost c x) := by
  classical
  have hcost : cost c (rebuilt r b a ystar k) = LB hm c r b a ystar := by
    rw [cost,Finset.sum_comm,LB,Z]
    simp only [pkObj]
    rw [partition_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hmem : a j∈Iprime r b a
    · have hjmem : j∈Jset a (a j) := by simp [Jset]
      rcases (hystar (a j) hmem).1.1 j hjmem with hy|hy
      · simp [rebuilt,hmem,hy,xPR]
      · simp [rebuilt,hmem,hy,(hk j).2]
    · simp [rebuilt,hmem,xPR]
  refine ⟨?_,hcost,?_⟩
  · constructor
    · intro i j
      dsimp only [rebuilt,xPR]
      split_ifs <;> simp
    · intro j
      unfold rebuilt
      by_cases hh : a j∈Iprime r b a ∧ ystar (a j) j=1
      · simp [hh]
      · simp [hh,xPR]
  · intro hfeas x hx
    rw [hcost]
    exact (knapsackBound_eq_lagrangean_bound hm c r b hb hr a ha ystar hystar).2.2 x hx
