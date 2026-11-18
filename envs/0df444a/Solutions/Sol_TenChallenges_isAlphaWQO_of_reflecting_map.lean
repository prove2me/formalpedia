-- Prove2me | solution 1 for TenChallenges.isAlphaWQO_of_reflecting_map
-- status  : ACCEPTED   (prove)
-- author  : @Davide
-- created : 2026-11-17T10:47:21.529003+00:00
-- url     : https://prove2.me/submissions/da4f26ca-e3c9-4284-9174-12cfb2f5a1e4

import Definitions.Def_TenChallenges_AlphaWQO

universe u

set_option linter.deprecated false

open Ordinal

namespace TenChallenges.AlphaWQOTransfer

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

/-! ### Pushing the hierarchy along a map -/

section Map

variable {P Q : Type u} (e : P → Q)

theorem cast_cast_self {A B : Type u} (h₁ : A = B) (h₂ : B = A) (x : A) :
    cast h₂ (cast h₁ x) = x := by
  subst h₁; rfl

/-- The map `V*_a(P) → V*_a(Q)` induced by `e`: apply `e` at level `0`,
take images at successor levels, and keep the tag at limit levels. -/
noncomputable def vmap (a : Ordinal.{u}) : VStar P a → VStar Q a :=
  Ordinal.limitRecOn (motive := fun a => VStar P a → VStar Q a) a
    (fun X => cast (VStar_zero Q).symm (e (cast (VStar_zero P) X)))
    (fun α ih X => cast (VStar_succ Q α).symm
      ⟨ih '' (cast (VStar_succ P α) X).val, (cast (VStar_succ P α) X).2.image ih⟩)
    (fun a ha ih X => cast (VStar_limit Q ha).symm
      ⟨(cast (VStar_limit P ha) X).1,
        ih _ (Ordinal.typein_lt_self _) (cast (VStar_limit P ha) X).2⟩)

theorem vmap_zero (X : VStar P 0) :
    cast (VStar_zero Q) (vmap e 0 X) = e (cast (VStar_zero P) X) := by
  unfold vmap
  rw [Ordinal.limitRecOn_zero]
  simp

theorem vmap_succ (α : Ordinal.{u}) (X : VStar P (Order.succ α)) :
    (cast (VStar_succ Q α) (vmap e (Order.succ α) X)).val =
      vmap e α '' (cast (VStar_succ P α) X).val := by
  conv_lhs => unfold vmap
  rw [Ordinal.limitRecOn_succ]
  exact congrArg Subtype.val (cast_cast_self _ _ _)

theorem vmap_limit {a : Ordinal.{u}} (ha : Order.IsSuccLimit a) (X : VStar P a) :
    cast (VStar_limit Q ha) (vmap e a X) =
      ⟨(cast (VStar_limit P ha) X).1,
        vmap e _ (cast (VStar_limit P ha) X).2⟩ := by
  conv_lhs => unfold vmap
  rw [Ordinal.limitRecOn_limit _ _ _ _ ha]
  simp only [cast_cast, cast_eq]
  rfl

end Map

/-! ### `vmap` reflects the game relation -/

section Reflect

variable {P Q : Type u} (leP : P → P → Prop) (leQ : Q → Q → Prop) (e : P → Q)
  (he : ∀ x y, leQ (e x) (e y) → leP x y)
include he

theorem reflect (a : Ordinal.{u}) :
    ∀ (b : Ordinal.{u}) (X : VStar P a) (Y : VStar P b),
      leStar leQ a (vmap e a X) b (vmap e b Y) → leStar leP a X b Y := by
  induction a using Ordinal.limitRecOn with
  | zero =>
    intro b
    induction b using Ordinal.limitRecOn with
    | zero =>
      intro X Y h
      rw [leStar_zero_zero] at h ⊢
      rw [vmap_zero, vmap_zero] at h
      exact he _ _ h
    | add_one β ihb =>
      show ∀ (X : VStar P 0) (Y : VStar P (Order.succ β)),
        leStar leQ 0 (vmap e 0 X) (Order.succ β) (vmap e (Order.succ β) Y) →
          leStar leP 0 X (Order.succ β) Y
      intro X Y h
      rw [leStar_zero_succ] at h ⊢
      obtain ⟨y', hy', h⟩ := h
      rw [vmap_succ] at hy'
      obtain ⟨y, hy, rfl⟩ := hy'
      exact ⟨y, hy, ihb X y h⟩
    | limit β hb ihb =>
      intro X Y h
      rw [leStar_zero_limit _ _ hb] at h ⊢
      rw [vmap_limit _ hb] at h
      exact ihb _ (Ordinal.typein_lt_self _) X _ h
  | add_one α iha =>
    show ∀ (b : Ordinal.{u}) (X : VStar P (Order.succ α)) (Y : VStar P b),
      leStar leQ (Order.succ α) (vmap e (Order.succ α) X) b (vmap e b Y) →
        leStar leP (Order.succ α) X b Y
    intro b
    induction b using Ordinal.limitRecOn with
    | zero =>
      intro X Y h
      rw [leStar_succ_zero] at h ⊢
      intro x hx
      apply iha 0 x Y
      apply h
      rw [vmap_succ]
      exact ⟨x, hx, rfl⟩
    | add_one β _ =>
      show ∀ (X : VStar P (Order.succ α)) (Y : VStar P (Order.succ β)),
        leStar leQ (Order.succ α) (vmap e (Order.succ α) X) (Order.succ β)
          (vmap e (Order.succ β) Y) → leStar leP (Order.succ α) X (Order.succ β) Y
      intro X Y h
      rw [leStar_succ_succ] at h ⊢
      intro x hx
      obtain ⟨y', hy', h⟩ := h (vmap e α x) (by rw [vmap_succ]; exact ⟨x, hx, rfl⟩)
      rw [vmap_succ] at hy'
      obtain ⟨y, hy, rfl⟩ := hy'
      exact ⟨y, hy, iha β x y h⟩
    | limit β hb ihb =>
      intro X Y h
      rw [leStar_succ_limit _ _ _ hb] at h ⊢
      rw [vmap_limit _ hb] at h
      exact ihb _ (Ordinal.typein_lt_self _) X _ h
  | limit a ha iha =>
    intro b X Y h
    rw [leStar_limit_left _ ha] at h ⊢
    rw [vmap_limit _ ha] at h
    exact iha _ (Ordinal.typein_lt_self _) b _ Y h

end Reflect

end TenChallenges.AlphaWQOTransfer

open TenChallenges.AlphaWQOTransfer in
theorem solution {P Q : Type u} (leP : P → P → Prop) (leQ : Q → Q → Prop) (e : P → Q)
    (he : ∀ x y, leQ (e x) (e y) → leP x y) (α : Ordinal.{u}) :
    IsAlphaWQO leQ α → IsAlphaWQO leP α := by
  intro hQ f
  obtain ⟨i, j, hij, h⟩ := hQ (fun n => vmap e α (f n))
  exact ⟨i, j, hij, reflect leP leQ e he α α (f i) (f j) h⟩
