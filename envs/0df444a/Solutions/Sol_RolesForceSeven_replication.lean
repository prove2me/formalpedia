-- Prove2me | solution 1 for RolesForceSeven.replication
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:56:37.809246+00:00
-- url     : https://prove2.me/submissions/fa5daca6-5132-44fe-9d6c-af1043ac4b02

import Mathlib
import Definitions.Def_RolesForceSeven_sts
import Definitions.Def_RolesForceSeven_fano

open RolesForceSeven

theorem solution (n : ℕ) (S : STS n) (x : Fin n) :
    2 * (S.lines.filter (fun l => x ∈ l)).card + 1 = n := by
  classical
  set L := S.lines.filter (fun l => x ∈ l) with hL
  have hcover : (Finset.univ.erase x : Finset (Fin n)) = L.biUnion (fun l => l.erase x) := by
    ext y
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_biUnion, hL,
      Finset.mem_filter]
    constructor
    · intro hy
      obtain ⟨l, ⟨hl, hxl, hyl⟩, -⟩ := S.pair_unique x y (Ne.symm hy)
      exact ⟨l, ⟨hl, hxl⟩, hy, hyl⟩
    · rintro ⟨l, -, hy, -⟩; exact hy
  have hdisj : (L : Set (Finset (Fin n))).PairwiseDisjoint (fun l => l.erase x) := by
    intro l hl l' hl' hne
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hL] at hl hl'
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy hy'
    rw [Finset.mem_erase] at hy hy'
    obtain ⟨m, -, hm⟩ := S.pair_unique x y (Ne.symm hy.1)
    exact hne ((hm l ⟨hl.1, hl.2, hy.2⟩).trans (hm l' ⟨hl'.1, hl'.2, hy'.2⟩).symm)
  have hcard := congrArg Finset.card hcover
  rw [Finset.card_biUnion hdisj, Finset.card_erase_of_mem (Finset.mem_univ x),
    Finset.card_univ, Fintype.card_fin] at hcard
  have hsum : ∑ l ∈ L, (l.erase x).card = ∑ l ∈ L, 2 := by
    apply Finset.sum_congr rfl
    intro l hl
    simp only [hL, Finset.mem_filter] at hl
    rw [Finset.card_erase_of_mem hl.2, S.card_three l hl.1]
  rw [hsum, Finset.sum_const, smul_eq_mul] at hcard
  have := x.pos
  omega

theorem W8_RolesForceSeven_three_lines (n : ℕ) (S : STS n) (role : Fin n → Finset (Fin n) → Fin 3)
    (h : RoleColouring S role) (x : Fin n) :
    (S.lines.filter (fun l => x ∈ l)).card = 3 := by
  classical
  have : (S.lines.filter (fun l => x ∈ l)).card = (Finset.univ : Finset (Fin 3)).card := by
    apply Finset.card_bij (fun l _ => role x l)
    · intros; exact Finset.mem_univ _
    · intro l hl l' hl' he
      simp only [Finset.mem_filter] at hl hl'
      exact h.2.2 x l hl.1 l' hl'.1 hl.2 hl'.2 he
    · intro ρ _
      obtain ⟨l, hl, hxl, hr⟩ := h.2.1 x ρ
      exact ⟨l, Finset.mem_filter.2 ⟨hl, hxl⟩, hr⟩
  simpa using this

theorem W8_RolesForceSeven_roles_force_seven (n : ℕ) (hn : 0 < n) (S : STS n)
    (role : Fin n → Finset (Fin n) → Fin 3) (h : RoleColouring S role) :
    n = 7 := by
  have h1 := solution n S ⟨0, hn⟩
  rw [W8_RolesForceSeven_three_lines n S role h ⟨0, hn⟩] at h1
  omega

theorem W8_RolesForceSeven_no_nine (S : STS 9) (role : Fin 9 → Finset (Fin 9) → Fin 3) :
    ¬ RoleColouring S role := by
  intro h
  have := W8_RolesForceSeven_roles_force_seven 9 (by norm_num) S role h
  omega

def W8_RolesForceSeven_role (x : Fin 7) (l : Finset (Fin 7)) : Fin 3 :=
  if x + 1 ∈ l ∧ x + 3 ∈ l then 0 else if x + 6 ∈ l ∧ x + 2 ∈ l then 1 else 2

set_option maxRecDepth 100000 in
theorem W8_RolesForceSeven_fano : ∃ role, RoleColouring fano role := by
  refine ⟨W8_RolesForceSeven_role, ?_, ?_, ?_⟩
  · have key : ∀ i : Fin 7, ∀ x ∈ fanoLine i, ∀ y ∈ fanoLine i,
        W8_RolesForceSeven_role x (fanoLine i) = W8_RolesForceSeven_role y (fanoLine i) →
          x = y := by decide
    intro l hl
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hl
    exact key i
  · have key : ∀ x : Fin 7, ∀ ρ : Fin 3, ∃ i : Fin 7, x ∈ fanoLine i ∧
        W8_RolesForceSeven_role x (fanoLine i) = ρ := by decide
    intro x ρ
    obtain ⟨i, h1, h2⟩ := key x ρ
    exact ⟨fanoLine i, Finset.mem_image_of_mem _ (Finset.mem_univ i), h1, h2⟩
  · have key : ∀ x : Fin 7, ∀ i j : Fin 7, x ∈ fanoLine i → x ∈ fanoLine j →
        W8_RolesForceSeven_role x (fanoLine i) = W8_RolesForceSeven_role x (fanoLine j) →
          fanoLine i = fanoLine j := by decide
    intro x l hl l' hl'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hl
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hl'
    exact key x i j
