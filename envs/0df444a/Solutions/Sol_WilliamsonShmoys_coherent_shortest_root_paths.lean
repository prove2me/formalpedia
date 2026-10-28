-- Prove2me | solution 1 for WilliamsonShmoys.coherent_shortest_root_paths
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:48:53.386645+00:00
-- url     : https://prove2.me/submissions/6de8dc3f-794b-4267-bca9-e753c8d881da

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

namespace A3S55CS

open SimpleGraph

variable {V : Type} (G : SimpleGraph V) (root : V)

theorem exists_parent (v : V) (hr : G.Reachable root v) (n : ℕ) (h : G.dist root v = n + 1) :
    ∃ p, G.Adj p v ∧ G.Reachable root p ∧ G.dist root p = n := by
  obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_dist
  have hlen : w.reverse.length = n + 1 := by simp [hw, h]
  cases hwr : w.reverse with
  | nil => rw [hwr] at hlen; simp at hlen
  | @cons _ p _ hadj q =>
    rw [hwr] at hlen
    simp at hlen
    refine ⟨p, hadj.symm, ⟨q.reverse⟩, ?_⟩
    apply le_antisymm
    · have := SimpleGraph.dist_le q.reverse
      simp at this; omega
    · obtain ⟨r, hr'⟩ := SimpleGraph.Reachable.exists_walk_length_eq_dist (⟨q.reverse⟩ : G.Reachable root p)
      have := SimpleGraph.dist_le (r.concat hadj.symm)
      simp at this; omega

noncomputable def W : (n : ℕ) → (v : V) → G.dist root v = n → G.Reachable root v → G.Walk root v
  | 0, v, h, hr => Walk.nil.copy rfl ((hr.dist_eq_zero_iff).1 h)
  | n + 1, v, h, hr =>
    (W n (exists_parent G root v hr n h).choose (exists_parent G root v hr n h).choose_spec.2.2
      (exists_parent G root v hr n h).choose_spec.2.1).concat
      (exists_parent G root v hr n h).choose_spec.1

theorem W_irrel (n m : ℕ) (v : V) (h : G.dist root v = n) (h' : G.dist root v = m)
    (hr hr' : G.Reachable root v) : W G root n v h hr = W G root m v h' hr' := by
  obtain rfl : n = m := h.symm.trans h'
  rfl

theorem W_length (n : ℕ) : ∀ (v : V) (h : G.dist root v = n) (hr : G.Reachable root v),
    (W G root n v h hr).length = n := by
  induction n with
  | zero => intro v h hr; simp [W]
  | succ n ih => intro v h hr; simp [W, ih]

theorem W_sub (n : ℕ) : ∀ (v : V) (h : G.dist root v = n) (hr : G.Reachable root v)
    (u : V) (m : ℕ) (hu : G.dist root u = m) (hru : G.Reachable root u),
    u ∈ (W G root n v h hr).support → (W G root m u hu hru).IsSubwalk (W G root n v h hr) := by
  induction n with
  | zero =>
    intro v h hr u m hu hru hmem
    have hv : root = v := (hr.dist_eq_zero_iff).1 h
    have huv : u = v := by
      simp [W] at hmem; rw [hmem, hv]
    subst huv
    rw [W_irrel G root m 0 _ hu h hru hr]
  | succ n ih =>
    intro v h hr u m hu hru hmem
    simp only [W, Walk.support_concat, List.mem_append,
      List.mem_singleton] at hmem ⊢
    rcases hmem with hmem | huv
    · exact (ih _ _ _ u m hu hru hmem).trans (Walk.isSubwalk_concat _ _)
    · subst huv
      rw [W_irrel G root m (n+1) _ hu h hru hr]
      simp only [W]
      exact Walk.isSubwalk_rfl _

end A3S55CS

theorem solution
    {V : Type} [Finite V] (G : SimpleGraph V) (root : V) :
    ∃ P : (v : {x : V // G.Reachable root x}) → G.Walk root v.val,
      (∀ v, (P v).IsPath ∧ (P v).length = G.dist root v.val) ∧
      (∀ u v : {x : V // G.Reachable root x},
        u.val ∈ (P v).support → (P u).IsSubwalk (P v)) := by
  refine ⟨fun v => A3S55CS.W G root _ v.val rfl v.2, fun v => ?_, fun u v hmem => ?_⟩
  · have hl := A3S55CS.W_length G root _ v.val rfl v.2
    exact ⟨SimpleGraph.Walk.isPath_of_length_eq_dist _ hl, hl⟩
  · exact A3S55CS.W_sub G root _ v.val rfl v.2 u.val _ rfl u.2 hmem

