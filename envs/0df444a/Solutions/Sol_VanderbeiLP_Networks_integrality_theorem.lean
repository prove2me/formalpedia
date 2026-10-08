-- Prove2me | solution 1 for VanderbeiLP.Networks.integrality_theorem
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T14:35:34.070546+00:00
-- url     : https://prove2.me/submissions/c207a8e6-bdb7-4df9-9fc9-aae83d9b2b71

/-
Theorem 14.2 (Integrality Theorem), Vanderbei's Linear Programming.

Let `x` be a basic feasible flow: a feasible flow vanishing off a set `T` of arcs whose columns of
the truncated incidence matrix are linearly independent. Two facts about `T` follow from the
independence alone.

* A walk in the undirected arc graph of `T \ {a}` from `i` to `j` gives a combination of columns
  of `T \ {a}` equal to `e_j - e_i`, the column of the arc `a = (i, j)`. So `a` and that walk would
  give a nontrivial dependency (`walk_comb`, `not_reachable`): no arc of `T` closes a cycle.
* Let `S` be the set of nodes reachable from `i` in `T \ {a}`. Summing the balance equations
  `Ax = -b` over `S`, every arc of `T` other than `a` has both ends on the same side of `S`, every
  arc outside `T` carries no flow, and `a` leaves `S`. Hence `x_a = sum_{k in S} b_k`, an integer.

Connectedness and `sum b = 0` are not needed.
-/
import Mathlib
import Definitions.Def_VanderbeiLP_Networks_Network

set_option autoImplicit false

namespace VanderbeiLP.Networks
open Finset

section IntLib
variable {N : Type*} [DecidableEq N]

theorem incidence_eq {i j : N} (h : i ≠ j) (k : N) :
    incidence k (i, j) = (if k = j then 1 else 0) - (if k = i then 1 else 0) := by
  unfold incidence
  by_cases h2 : k = j
  · subst h2; simp [Ne.symm h]
  · by_cases h1 : k = i
    · subst h1; simp [h2]
    · simp [h1, h2]

theorem sum_incidence (A : Finset (N × N)) (hA : IsNetwork A) (C : Finset N) (a : N × N)
    (ha : a ∈ A) :
    ∑ k ∈ C, incidence k a = (if a.2 ∈ C then 1 else 0) - (if a.1 ∈ C then 1 else 0) := by
  have h := hA a ha
  obtain ⟨i, j⟩ := a
  simp only at h ⊢
  simp only [incidence_eq h, Finset.sum_sub_distrib, Finset.sum_ite_eq']

/-- A walk in the arc graph gives a combination of arc columns equal to `e_v - e_u`. -/
theorem walk_comb (T' : Finset (N × N)) {u v : N} (p : (arcGraph T').Walk u v) :
    ∃ g : N × N → ℝ, ∀ k, ∑ b ∈ T', g b * incidence k b =
      (if k = v then 1 else 0) - (if k = u then 1 else 0) := by
  induction p with
  | nil => exact ⟨fun _ => 0, fun k => by simp⟩
  | @cons u w v hadj p ih =>
    obtain ⟨g, hg⟩ := ih
    have hadj' := hadj
    unfold arcGraph at hadj'
    rw [SimpleGraph.fromEdgeSet_adj] at hadj'
    obtain ⟨⟨b, hb0, hbe⟩, hne⟩ := hadj'
    have hb : b ∈ T' := Finset.mem_coe.1 hb0
    rcases Sym2.eq_iff.1 hbe with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨fun b' => g b' + if b' = b then 1 else 0, fun k => ?_⟩
      have : ∑ b' ∈ T', (g b' + if b' = b then (1 : ℝ) else 0) * incidence k b' =
          (∑ b' ∈ T', g b' * incidence k b') + incidence k b := by
        simp [add_mul, Finset.sum_add_distrib, ite_mul, hb]
      rw [this, hg k]
      have hb' : b = (u, w) := Prod.ext h1 h2
      rw [hb', incidence_eq hne]
      ring
    · refine ⟨fun b' => g b' - if b' = b then 1 else 0, fun k => ?_⟩
      have : ∑ b' ∈ T', (g b' - if b' = b then (1 : ℝ) else 0) * incidence k b' =
          (∑ b' ∈ T', g b' * incidence k b') - incidence k b := by
        simp [sub_mul, Finset.sum_sub_distrib, ite_mul, hb]
      rw [this, hg k]
      have hb' : b = (w, u) := Prod.ext h1 h2
      rw [hb', incidence_eq (Ne.symm hne)]
      ring

end IntLib

section IntLib2
variable {N : Type*} [Fintype N] [DecidableEq N]

theorem indep_zero (r : N) (T : Finset (N × N))
    (hind : LinearIndependent ℝ (fun a : T => fun k : {k : N // k ≠ r} => truncIncidence r k a.1))
    (g : N × N → ℝ) (hg : ∀ k, k ≠ r → ∑ b ∈ T, g b * incidence k b = 0) :
    ∀ b ∈ T, g b = 0 := by
  rw [Fintype.linearIndependent_iff] at hind
  intro b hb
  refine hind (fun a => g a.1) ?_ ⟨b, hb⟩
  funext k
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.zero_apply]
  have := hg k.1 k.2
  rw [← Finset.sum_coe_sort T] at this
  exact this

theorem not_reachable (r : N) (T : Finset (N × N))
    (hind : LinearIndependent ℝ (fun a : T => fun k : {k : N // k ≠ r} => truncIncidence r k a.1))
    (a : N × N) (ha : a ∈ T) (hne : a.1 ≠ a.2) :
    ¬ (arcGraph (T.erase a)).Reachable a.1 a.2 := by
  rintro ⟨p⟩
  obtain ⟨g, hg⟩ := walk_comb (T.erase a) p
  have key := indep_zero r T hind (fun b => if b = a then -1 else g b) ?_ a ha
  · simp at key
  · intro k _
    rw [← Finset.add_sum_erase T _ ha]
    have : ∑ b ∈ T.erase a, (if b = a then (-1 : ℝ) else g b) * incidence k b =
        ∑ b ∈ T.erase a, g b * incidence k b :=
      Finset.sum_congr rfl (fun b hb => by rw [if_neg (Finset.ne_of_mem_erase hb)])
    rw [this, hg k]
    obtain ⟨i, j⟩ := a
    simp only [if_true] 
    rw [incidence_eq hne]
    ring


theorem integrality_core (A : Finset (N × N)) (hA : IsNetwork A) (b : N → ℝ)
    (hb : ∀ i, ∃ z : ℤ, b i = z) (r : N) (x : N × N → ℝ) (hx : IsBasicFeasibleFlow A b r x) :
    ∀ a ∈ A, ∃ z : ℤ, x a = z := by
  classical
  obtain ⟨⟨hbal, _⟩, T, hTA, ⟨_, hind⟩, hzero⟩ := hx
  intro a haA
  by_cases haT : a ∈ T
  swap
  · exact ⟨0, by simp [hzero a haA haT]⟩
  have hne : a.1 ≠ a.2 := hA a haA
  have hnr := not_reachable r T hind a haT hne
  set S : Finset N := Finset.univ.filter (fun k => (arcGraph (T.erase a)).Reachable a.1 k) with hS
  have hmemS : ∀ k, k ∈ S ↔ (arcGraph (T.erase a)).Reachable a.1 k := fun k => by simp [hS]
  have h1 : ∑ k ∈ S, ∑ a' ∈ A, incidence k a' * x a' = -∑ k ∈ S, b k := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun k _ => hbal k)
  have h2 : ∑ k ∈ S, ∑ a' ∈ A, incidence k a' * x a' =
      ∑ a' ∈ A, x a' * ((if a'.2 ∈ S then (1 : ℝ) else 0) - (if a'.1 ∈ S then 1 else 0)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a' ha' => ?_)
    rw [← Finset.sum_mul, sum_incidence A hA S a' ha']
    ring
  have h3 : ∑ a' ∈ A, x a' * ((if a'.2 ∈ S then (1 : ℝ) else 0) - (if a'.1 ∈ S then 1 else 0)) =
      -x a := by
    rw [Finset.sum_eq_single_of_mem a haA]
    · have h1S : a.1 ∈ S := (hmemS _).2 (SimpleGraph.Reachable.refl _)
      have h2S : a.2 ∉ S := fun h => hnr ((hmemS _).1 h)
      simp [h1S, h2S]
    · intro a' ha' hne'
      by_cases ha'T : a' ∈ T
      · have hadj : (arcGraph (T.erase a)).Adj a'.1 a'.2 := by
          unfold arcGraph
          rw [SimpleGraph.fromEdgeSet_adj]
          exact ⟨⟨a', Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hne', ha'T⟩), rfl⟩, hA a' ha'⟩
        have : a'.2 ∈ S ↔ a'.1 ∈ S := by
          rw [hmemS, hmemS]
          exact ⟨fun h => h.trans hadj.reachable.symm, fun h => h.trans hadj.reachable⟩
        by_cases h : a'.1 ∈ S
        · simp [h, this.2 h]
        · simp [h, show a'.2 ∉ S from fun h' => h (this.1 h')]
      · simp [hzero a' ha' ha'T]
  obtain ⟨z, hz⟩ := Classical.axiomOfChoice hb
  refine ⟨∑ k ∈ S, z k, ?_⟩
  have : x a = ∑ k ∈ S, b k := by linarith
  rw [this]
  push_cast
  exact Finset.sum_congr rfl (fun k _ => hz k)

end IntLib2
end VanderbeiLP.Networks

open VanderbeiLP.Networks in
theorem solution {N : Type*} [Fintype N] [DecidableEq N]
    (A : Finset (N × N)) (hA : IsNetwork A) (hconn : IsConnectedNetwork A)
    (b : N → ℝ) (hsum : ∑ i, b i = 0) (hb : ∀ i, ∃ z : ℤ, b i = z)
    (r : N) (x : N × N → ℝ) (hx : IsBasicFeasibleFlow A b r x) :
    ∀ a ∈ A, ∃ z : ℤ, x a = z :=
  integrality_core A hA b hb r x hx
