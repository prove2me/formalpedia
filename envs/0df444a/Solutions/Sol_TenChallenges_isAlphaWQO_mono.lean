-- Prove2me | solution 1 for TenChallenges.isAlphaWQO_mono
-- status  : ACCEPTED   (prove)
-- author  : @Davide
-- created : 2026-11-17T15:27:10.164043+00:00
-- url     : https://prove2.me/submissions/9ff0d881-4c11-4254-a2c0-0f077cdc9c84

import Definitions.Def_TenChallenges_AlphaWQO

universe u

set_option linter.deprecated false

open Ordinal

namespace TenChallenges.AlphaWQOMono

/-! ### Unfolding equations for `leStar` -/

section Unfold

variable {Q : Type u} (le : Q → Q → Prop)

theorem leStar_zero_zero (X Y : VStar Q 0) :
    leStar le 0 X 0 Y ↔ le (cast (VStar_zero Q) X) (cast (VStar_zero Q) Y) := by
  unfold leStar
  simp only [Ordinal.limitRecOn_zero]

theorem leStar_zero_succ (X : VStar Q 0) (β : Ordinal.{u}) (Y : VStar Q (Order.succ β)) :
    leStar le 0 X (Order.succ β) Y ↔
      ∃ y ∈ (cast (VStar_succ Q β) Y).val, leStar le 0 X β y := by
  unfold leStar
  simp only [Ordinal.limitRecOn_zero, Ordinal.limitRecOn_succ]

theorem leStar_zero_limit (X : VStar Q 0) {β : Ordinal.{u}} (hb : Order.IsSuccLimit β)
    (Y : VStar Q β) :
    leStar le 0 X β Y ↔
      leStar le 0 X (Ordinal.typein (α := β.ToType) (· < ·) (cast (VStar_limit Q hb) Y).1)
        (cast (VStar_limit Q hb) Y).2 := by
  unfold leStar
  simp only [Ordinal.limitRecOn_zero, Ordinal.limitRecOn_limit _ _ _ _ hb]

theorem leStar_succ_zero (α : Ordinal.{u}) (X : VStar Q (Order.succ α)) (Y : VStar Q 0) :
    leStar le (Order.succ α) X 0 Y ↔
      ∀ x ∈ (cast (VStar_succ Q α) X).val, leStar le α x 0 Y := by
  conv_lhs => unfold leStar
  simp only [Ordinal.limitRecOn_succ, Ordinal.limitRecOn_zero]
  rfl

theorem leStar_succ_succ (α : Ordinal.{u}) (X : VStar Q (Order.succ α)) (β : Ordinal.{u})
    (Y : VStar Q (Order.succ β)) :
    leStar le (Order.succ α) X (Order.succ β) Y ↔
      ∀ x ∈ (cast (VStar_succ Q α) X).val,
        ∃ y ∈ (cast (VStar_succ Q β) Y).val, leStar le α x β y := by
  conv_lhs => unfold leStar
  simp only [Ordinal.limitRecOn_succ]
  rfl

theorem leStar_succ_limit (α : Ordinal.{u}) (X : VStar Q (Order.succ α)) {β : Ordinal.{u}}
    (hb : Order.IsSuccLimit β) (Y : VStar Q β) :
    leStar le (Order.succ α) X β Y ↔
      leStar le (Order.succ α) X
        (Ordinal.typein (α := β.ToType) (· < ·) (cast (VStar_limit Q hb) Y).1)
        (cast (VStar_limit Q hb) Y).2 := by
  unfold leStar
  simp only [Ordinal.limitRecOn_succ, Ordinal.limitRecOn_limit _ _ _ _ hb]

theorem leStar_limit_left {α : Ordinal.{u}} (ha : Order.IsSuccLimit α) (X : VStar Q α)
    (β : Ordinal.{u}) (Y : VStar Q β) :
    leStar le α X β Y ↔
      leStar le (Ordinal.typein (α := α.ToType) (· < ·) (cast (VStar_limit Q ha) X).1)
        (cast (VStar_limit Q ha) X).2 β Y := by
  conv_lhs => unfold leStar
  rw [Ordinal.limitRecOn_limit _ _ _ _ ha]
  rfl

end Unfold


section Mono

variable {Q : Type u} (le : Q → Q → Prop)

theorem cast_cast_self {A B : Type u} (h₁ : A = B) (h₂ : B = A) (x : A) :
    cast h₂ (cast h₁ x) = x := by
  subst h₁; rfl

/-- Unwrapping a limit-level element on the right, for an arbitrary left level. -/
theorem leStar_limit_right (a : Ordinal.{u}) :
    ∀ (X : VStar Q a) {b : Ordinal.{u}} (hb : Order.IsSuccLimit b) (Y : VStar Q b),
      leStar le a X b Y ↔
        leStar le a X (Ordinal.typein (α := b.ToType) (· < ·) (cast (VStar_limit Q hb) Y).1)
          (cast (VStar_limit Q hb) Y).2 := by
  induction a using Ordinal.limitRecOn with
  | zero => intro X b hb Y; exact leStar_zero_limit le X hb Y
  | add_one α _ =>
    show ∀ (X : VStar Q (Order.succ α)) {b : Ordinal.{u}} (hb : Order.IsSuccLimit b)
      (Y : VStar Q b), _
    intro X b hb Y; exact leStar_succ_limit le α X hb Y
  | limit a ha iha =>
    intro X b hb Y
    rw [leStar_limit_left le ha, leStar_limit_left le ha]
    exact iha _ (Ordinal.typein_lt_self _) _ hb Y

/-- Transport of `≤*` along an equality of levels. -/
theorem leStar_transport {a b : Ordinal.{u}} (h : a = b) (X Y : VStar Q b) :
    leStar le a (cast (congrArg (VStar Q) h.symm) X) a (cast (congrArg (VStar Q) h.symm) Y) ↔
      leStar le b X b Y := by
  subst h; rfl

/-- Successor step: singletons embed level `γ` into level `γ + 1`. -/
theorem isAlphaWQO_of_succ (γ : Ordinal.{u}) :
    IsAlphaWQO le (Order.succ γ) → IsAlphaWQO le γ := by
  intro hw f
  obtain ⟨i, j, hij, h⟩ :=
    hw (fun n => cast (VStar_succ Q γ).symm ⟨{f n}, Set.singleton_nonempty _⟩)
  refine ⟨i, j, hij, ?_⟩
  have h' : leStar le (Order.succ γ)
      (cast (VStar_succ Q γ).symm ⟨{f i}, Set.singleton_nonempty _⟩) (Order.succ γ)
      (cast (VStar_succ Q γ).symm ⟨{f j}, Set.singleton_nonempty _⟩) := h
  rw [leStar_succ_succ, cast_cast_self, cast_cast_self] at h'
  obtain ⟨y, hy, hxy⟩ := h' (f i) rfl
  rw [Set.mem_singleton_iff.mp hy] at hxy
  exact hxy

/-- Limit step: tagging embeds level `β` into a limit level `l > β`. -/
theorem isAlphaWQO_of_limit {l : Ordinal.{u}} (hl : Order.IsSuccLimit l) {β : Ordinal.{u}}
    (hβ : β < l) : IsAlphaWQO le l → IsAlphaWQO le β := by
  intro hw f
  have hk : Ordinal.typein (α := l.ToType) (· < ·) (Ordinal.ToType.mk ⟨β, hβ⟩) = β :=
    congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply ⟨β, hβ⟩)
  obtain ⟨i, j, hij, h⟩ := hw (fun n => cast (VStar_limit Q hl).symm
    ⟨Ordinal.ToType.mk ⟨β, hβ⟩, cast (congrArg (VStar Q) hk.symm) (f n)⟩)
  refine ⟨i, j, hij, ?_⟩
  have h' : leStar le l (cast (VStar_limit Q hl).symm
      ⟨Ordinal.ToType.mk ⟨β, hβ⟩, cast (congrArg (VStar Q) hk.symm) (f i)⟩) l
      (cast (VStar_limit Q hl).symm
      ⟨Ordinal.ToType.mk ⟨β, hβ⟩, cast (congrArg (VStar Q) hk.symm) (f j)⟩) := h
  rw [leStar_limit_left le hl, leStar_limit_right le _ _ hl, cast_cast_self,
    cast_cast_self] at h'
  exact (leStar_transport le hk (f i) (f j)).1 h'

end Mono

end TenChallenges.AlphaWQOMono

open TenChallenges.AlphaWQOMono in
theorem solution {Q : Type u} (le : Q → Q → Prop) {α β : Ordinal.{u}} (h : β ≤ α) :
    IsAlphaWQO le α → IsAlphaWQO le β := by
  induction α using Ordinal.limitRecOn generalizing β with
  | zero =>
    intro hw
    rw [nonpos_iff_eq_zero.mp h]
    exact hw
  | add_one γ ih =>
    intro hw
    rcases Order.le_succ_iff_eq_or_le.mp h with rfl | hb
    · exact hw
    · exact ih hb (isAlphaWQO_of_succ le γ hw)
  | limit l hl _ =>
    intro hw
    rcases h.lt_or_eq with hlt | rfl
    · exact isAlphaWQO_of_limit le hl hlt hw
    · exact hw
