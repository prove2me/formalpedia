-- Prove2me | solution 1 for WilliamsonShmoys.indepSet_disjoint_union_split
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T11:23:59.776574+00:00
-- url     : https://prove2.me/submissions/176a0d41-9adf-444a-ac45-1ebe69c52c7d

import Mathlib

set_option autoImplicit false
open scoped BigOperators

theorem solution {m n : ℕ} (H : Fin m → SimpleGraph (Fin n)) (w : Fin m × Fin n → ℝ)
    (A : Finset (Fin m × Fin n))
    (hA : (SimpleGraph.fromRel (fun (u v : Fin m × Fin n) => u.1 = v.1 ∧ (H u.1).Adj u.2 v.2)).IsIndepSet
      (A : Set (Fin m × Fin n)))
    (hopt : ∀ S : Finset (Fin m × Fin n),
      (SimpleGraph.fromRel (fun (u v : Fin m × Fin n) => u.1 = v.1 ∧ (H u.1).Adj u.2 v.2)).IsIndepSet
        (S : Set (Fin m × Fin n)) →
      ∑ x ∈ S, w x ≤ ∑ x ∈ A, w x)
    (j : Fin m) (S : Finset (Fin n)) (hS : (H j).IsIndepSet (S : Set (Fin n))) :
    ∑ a ∈ S, w (j, a) ≤ ∑ x ∈ A.filter (fun x => x.1 = j), w x := by
  classical
  set U := SimpleGraph.fromRel (fun (u v : Fin m × Fin n) => u.1 = v.1 ∧ (H u.1).Adj u.2 v.2)
  let ι : Fin n ↪ Fin m × Fin n := ⟨fun a => (j, a), fun a b e => congrArg Prod.snd e⟩
  let A' := A.filter (fun x => x.1 ≠ j) ∪ S.map ι
  have hdisj : Disjoint (A.filter (fun x => x.1 ≠ j)) (S.map ι) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_filter] at hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hx'
    exact hx.2 rfl
  have hind : U.IsIndepSet (A' : Set (Fin m × Fin n)) := by
    intro x hx y hy hxy hadj
    simp only [A', Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_map] at hx hy
    have hadj' := hadj
    rw [SimpleGraph.fromRel_adj] at hadj'
    obtain ⟨-, hr⟩ := hadj'
    have hfst : x.1 = y.1 := by rcases hr with ⟨h, -⟩ | ⟨h, -⟩ <;> [exact h; exact h.symm]
    rcases hx with ⟨hxA, hxj⟩ | ⟨a, ha, rfl⟩ <;> rcases hy with ⟨hyA, hyj⟩ | ⟨b, hb, rfl⟩
    · exact hA hxA hyA hxy hadj
    · exact hxj hfst
    · exact hyj hfst.symm
    · have hab : a ≠ b := fun e => hxy (by rw [e])
      rcases hr with ⟨-, h⟩ | ⟨-, h⟩
      · exact hS ha hb hab h
      · exact hS hb ha (Ne.symm hab) h
  have h1 := hopt A' hind
  rw [Finset.sum_union hdisj, Finset.sum_map] at h1
  have h2 := Finset.sum_filter_add_sum_filter_not A (fun x => x.1 = j) w
  have h3 : ∑ a ∈ S, w (ι a) = ∑ a ∈ S, w (j, a) := rfl
  simp only [ne_eq] at h1
  linarith
