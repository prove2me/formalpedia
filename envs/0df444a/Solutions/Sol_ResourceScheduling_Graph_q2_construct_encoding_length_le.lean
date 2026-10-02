-- Prove2me | solution 1 for ResourceScheduling.Graph.q2_construct_encoding_length_le
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T05:29:22.710527+00:00
-- url     : https://prove2.me/submissions/95b89647-b3bb-428e-be42-4c4cf8730779

import Definitions.Def_ResourceScheduling_Graph_Construction

set_option autoImplicit false

open ResourceScheduling.Graph

private theorem unary_length (n : ℕ) : (unary n).length = n + 1 := by
  simp [unary]

private theorem flatMap_length_le {α β : Type} (xs : List α)
    (f : α → List β) (b : ℕ) (h : ∀ x ∈ xs, (f x).length ≤ b) :
    (xs.flatMap f).length ≤ xs.length * b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (by intro a ha; exact h a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      Nat.add_mul, Nat.one_mul]
    omega

private theorem flatMap_length_eq {α β : Type} (xs : List α)
    (f : α → List β) (b : ℕ) (h : ∀ x ∈ xs, (f x).length = b) :
    (xs.flatMap f).length = xs.length * b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (by intro a ha; exact h a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      Nat.add_mul, Nat.one_mul]
    omega

private theorem graph_code_length (d : GraphData) :
    (encGraph d).length = d.t + 1 + (3 * d.t) * (3 * d.t) := by
  unfold encGraph
  rw [List.length_append]
  have h := flatMap_length_eq (List.finRange (3 * d.t))
    (fun i => (List.finRange (3 * d.t)).map fun j =>
      if d.G.Adj i j then Letter.one else Letter.sep) (3 * d.t) (by simp)
  simpa only [unary_length, List.length_finRange] using congrArg (fun n => d.t + 1 + n) h

private theorem resources_length_le {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] : (nonEdgeList G).length ≤ N * N := by
  unfold nonEdgeList
  apply (flatMap_length_le _ _ N ?_).trans_eq (by simp)
  intro j hj
  simpa using List.length_filter_le
    (fun k : Fin N => decide (j < k ∧ ¬ G.Adj j k)) (List.finRange N)

private theorem data_code_length_le (x : ResDot11Data) :
    x.enc.length ≤ x.n + x.l + 2 * x.n * x.l + x.y + 3 := by
  have hrow : ∀ h : Fin x.l,
      ((List.finRange x.n).flatMap fun j => unary (x.r h j)).length ≤ x.n * 2 := by
    intro h
    apply (flatMap_length_le _ _ 2 ?_).trans_eq (by simp)
    intro j hj
    simpa [unary] using Nat.add_le_add_right (x.r_le h j) 1
  have hall := flatMap_length_le (List.finRange x.l)
    (fun h => (List.finRange x.n).flatMap fun j => unary (x.r h j)) (x.n * 2)
    (by intro h hh; exact hrow h)
  simp only [List.length_finRange] at hall
  simp only [ResDot11Data.enc, List.length_append, unary_length]
  nlinarith

/-- A size bound for the exact unary encoding used by the mission.
This proves output size, not Turing-machine running time. -/
theorem solution (d : GraphData) :
    (encQ2 (![2, 1], reduce d)).length ≤ 5 * (encGraph d).length ^ 2 + 8 := by
  have hg := graph_code_length d
  have hl := resources_length_le d.G
  have hd := data_code_length_le (reduce d)
  have hn : 3 * d.t ≤ (encGraph d).length := by
    have := Nat.le_mul_self (3 * d.t)
    omega
  have ht : d.t ≤ (encGraph d).length := by omega
  have hr : (nonEdgeList d.G).length ≤ (encGraph d).length := by omega
  have hmul := Nat.mul_le_mul hn hr
  have hs := Nat.le_mul_self (encGraph d).length
  change (reduce d).enc.length ≤
    3 * d.t + (nonEdgeList d.G).length + 2 * (3 * d.t) * (nonEdgeList d.G).length + d.t + 3 at hd
  simp only [encQ2, List.length_append, unary, List.length_replicate,
    List.length_cons, List.length_nil, Matrix.cons_val_zero, Matrix.cons_val_one]
  change 3 + 2 + (reduce d).enc.length ≤ _
  nlinarith

#print axioms solution
