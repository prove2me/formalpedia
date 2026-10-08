-- Prove2me | solution 1 for VanderbeiLP.Networks.flow_le_cut_capacity
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T14:14:36.486046+00:00
-- url     : https://prove2.me/submissions/98bd3bc4-860b-42bf-ab6c-672b2032b2a7

/-
Eq. (15.8) of Vanderbei's Linear Programming: a feasible flow of the maximum-flow problem has
value `x_{ts}` at most the capacity of every cut `C`.

Summing the flow-balance equations over the nodes of `C` shows that the net flow across the cut
equals `x_{ts}` (the extra arc `(t, s)` leaves `C ∌ t` and enters `C ∋ s`). The flow into `C` is
nonnegative and the flow out of `C` is at most the sum of the capacities of the arcs leaving `C`.
-/
import Mathlib
import Definitions.Def_VanderbeiLP_Networks_MaxFlow

set_option autoImplicit false

namespace VanderbeiLP.Networks
open Finset

section FlowLib
variable {N : Type*} [DecidableEq N]

/-- Inflow minus outflow of `f` at `k`, through the incidence matrix. -/
noncomputable def netOf (A : Finset (N × N)) (f : N × N → ℝ) (k : N) : ℝ :=
  ∑ a ∈ A, incidence k a * f a

theorem netOf_eq (A : Finset (N × N)) (hA : IsNetwork A) (f : N × N → ℝ) (k : N) :
    netOf A f k = (∑ a ∈ A.filter (fun a => a.2 = k), f a) - ∑ a ∈ A.filter (fun a => a.1 = k), f a := by
  unfold netOf
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  have h := hA a ha
  obtain ⟨i, j⟩ := a
  simp only at h
  unfold incidence
  by_cases h2 : k = j
  · have h1 : i ≠ k := fun e => h (e.trans h2)
    simp [h2, h1, h]
  · by_cases h1 : k = i
    · simp [h1, h2, h, Ne.symm h]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]


theorem sum_incidence (A : Finset (N × N)) (hA : IsNetwork A) (C : Finset N) (a : N × N) (ha : a ∈ A) :
    ∑ k ∈ C, incidence k a = (if a.2 ∈ C then 1 else 0) - (if a.1 ∈ C then 1 else 0) := by
  have h := hA a ha
  obtain ⟨i, j⟩ := a
  simp only at h ⊢
  have : ∀ k : N, incidence k (i, j) = (if j = k then 1 else 0) - (if i = k then 1 else 0) := by
    intro k
    unfold incidence
    by_cases h2 : k = j
    · subst h2; simp [h]
    · by_cases h1 : k = i
      · subst h1; simp [Ne.symm h2, h2]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq]

theorem cut_identity (A : Finset (N × N)) (hA : IsNetwork A) (u : N × N → ℝ) (s t : N)
    (x : N × N → ℝ) (xts : ℝ) (hx : IsMaxFlowFeasible A u s t x xts) (C : Finset N)
    (hC : IsCut s t C) :
    (∑ a ∈ A.filter (fun a => a.1 ∈ C ∧ a.2 ∉ C), x a) -
      (∑ a ∈ A.filter (fun a => a.1 ∉ C ∧ a.2 ∈ C), x a) = xts := by
  obtain ⟨hs, ht⟩ := hC
  have hcons : ∀ k, netOf A x k + (if k = s then xts else 0) - (if k = t then xts else 0) = 0 := by
    intro k
    have := hx.2.2 k
    rw [netOf_eq A hA]
    linarith
  have h1 : ∑ k ∈ C, (netOf A x k + (if k = s then xts else 0) - (if k = t then xts else 0)) = 0 :=
    Finset.sum_eq_zero (fun k _ => hcons k)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
    if_pos hs, if_neg ht] at h1
  have h2 : ∑ k ∈ C, netOf A x k =
      (∑ a ∈ A.filter (fun a => a.1 ∉ C ∧ a.2 ∈ C), x a) -
        ∑ a ∈ A.filter (fun a => a.1 ∈ C ∧ a.2 ∉ C), x a := by
    unfold netOf
    rw [Finset.sum_comm, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [← Finset.sum_mul, sum_incidence A hA C a ha]
    by_cases h1 : a.1 ∈ C <;> by_cases h2 : a.2 ∈ C <;> simp [h1, h2]
  linarith


theorem flow_le_cap (A : Finset (N × N)) (hA : IsNetwork A) (u : N × N → ℝ) (s t : N)
    (x : N × N → ℝ) (xts : ℝ) (hx : IsMaxFlowFeasible A u s t x xts) (C : Finset N)
    (hC : IsCut s t C) : xts ≤ cutCapacity A u C := by
  have h := cut_identity A hA u s t x xts hx C hC
  have hin : 0 ≤ ∑ a ∈ A.filter (fun a => a.1 ∉ C ∧ a.2 ∈ C), x a :=
    Finset.sum_nonneg (fun a ha => (hx.1 a (Finset.mem_filter.1 ha).1).1)
  have hout : ∑ a ∈ A.filter (fun a => a.1 ∈ C ∧ a.2 ∉ C), x a ≤ cutCapacity A u C :=
    Finset.sum_le_sum (fun a ha => (hx.1 a (Finset.mem_filter.1 ha).1).2)
  linarith

end FlowLib

end VanderbeiLP.Networks

open VanderbeiLP.Networks in
theorem solution {N : Type*} [Fintype N] [DecidableEq N]
    (A : Finset (N × N)) (hA : IsNetwork A) (u : N × N → ℝ) (s t : N)
    (x : N × N → ℝ) (xts : ℝ) (hx : IsMaxFlowFeasible A u s t x xts)
    (C : Finset N) (hC : IsCut s t C) :
    xts ≤ cutCapacity A u C := flow_le_cap A hA u s t x xts hx C hC
