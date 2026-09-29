-- Prove2me | solution 2 for RolesForceSeven.roles_force_seven
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-24T10:10:46.009985+00:00
-- url     : https://prove2.me/submissions/fb859471-3b45-48bd-a771-f1b99d68f48a

import Mathlib
import Definitions.Def_RolesForceSeven_sts

namespace RolesForceSevenSol
open RolesForceSeven

theorem replication (n : ℕ) (S : STS n) (x : Fin n) :
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

theorem three_lines (n : ℕ) (S : STS n) (role : Fin n → Finset (Fin n) → Fin 3)
    (h : RoleColouring S role) (x : Fin n) :
    (S.lines.filter (fun l => x ∈ l)).card = 3 := by
  obtain ⟨-, hcomp, hmin⟩ := h
  set T := S.lines.filter (fun l => x ∈ l) with hT
  have hinj : Set.InjOn (fun l => role x l) T := by
    intro l hl l' hl' he
    simp only [Finset.coe_filter, hT, Set.mem_ofPred_eq] at hl hl'
    exact hmin x l hl.1 l' hl'.1 hl.2 hl'.2 he
  have himage : T.image (fun l => role x l) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro ρ
    obtain ⟨l, hl, hxl, hρ⟩ := hcomp x ρ
    exact Finset.mem_image.2 ⟨l, by simp [hT, hl, hxl], hρ⟩
  rw [← Finset.card_image_of_injOn hinj, himage, Finset.card_univ, Fintype.card_fin]

end RolesForceSevenSol

open RolesForceSevenSol
open RolesForceSeven

theorem solution (n : ℕ) (hn : 0 < n) (S : STS n)
    (role : Fin n → Finset (Fin n) → Fin 3) (h : RoleColouring S role) :
    n = 7 := by
  have := replication n S ⟨0, hn⟩
  rw [three_lines n S role h ⟨0, hn⟩] at this
  omega
