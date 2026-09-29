-- Prove2me | solution 2 for RolesForceSeven.replication
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-24T10:10:44.65664+00:00
-- url     : https://prove2.me/submissions/54facdbc-50b0-44d3-9afa-24a8ce5b3b1b

import Mathlib
import Definitions.Def_RolesForceSeven_sts

open RolesForceSeven

theorem solution (n : ℕ) (S : STS n) (x : Fin n) :
    2 * (S.lines.filter (fun l => x ∈ l)).card + 1 = n := by
  set T := S.lines.filter (fun l => x ∈ l) with hT
  -- the other points are covered by the lines through x, minus x
  have hcover : Finset.univ.erase x = T.biUnion (fun l => l.erase x) := by
    ext y
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_biUnion, hT,
      Finset.mem_filter]
    constructor
    · intro hy
      obtain ⟨l, ⟨hl, hxl, hyl⟩, -⟩ := S.pair_unique x y (Ne.symm hy)
      exact ⟨l, ⟨hl, hxl⟩, hy, hyl⟩
    · rintro ⟨l, -, hy, -⟩; exact hy
  -- and two lines through x share no other point
  have hdisj : (T : Set (Finset (Fin n))).PairwiseDisjoint (fun l => l.erase x) := by
    intro l hl l' hl' hne
    simp only [Finset.coe_filter, hT, Set.mem_ofPred_eq] at hl hl'
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy hy'
    rw [Finset.mem_erase] at hy hy'
    obtain ⟨m, -, hm⟩ := S.pair_unique x y (Ne.symm hy.1)
    exact hne ((hm l ⟨hl.1, hl.2, hy.2⟩).trans (hm l' ⟨hl'.1, hl'.2, hy'.2⟩).symm)
  have hcard : (Finset.univ.erase x).card = 2 * T.card := by
    rw [hcover, Finset.card_biUnion hdisj]
    rw [Finset.sum_congr rfl (g := fun _ => 2) (fun l hl => by
      simp only [hT, Finset.mem_filter] at hl
      rw [Finset.card_erase_of_mem hl.2, S.card_three l hl.1])]
    simp [mul_comm]
  rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Fintype.card_fin] at hcard
  have := x.pos
  omega
