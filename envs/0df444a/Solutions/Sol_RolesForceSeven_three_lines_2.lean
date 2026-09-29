-- Prove2me | solution 2 for RolesForceSeven.three_lines
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-24T10:10:45.303787+00:00
-- url     : https://prove2.me/submissions/18de00e6-cf08-4373-adad-43a4077cfe08

import Mathlib
import Definitions.Def_RolesForceSeven_sts

open RolesForceSeven

theorem solution (n : ℕ) (S : STS n) (role : Fin n → Finset (Fin n) → Fin 3)
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
