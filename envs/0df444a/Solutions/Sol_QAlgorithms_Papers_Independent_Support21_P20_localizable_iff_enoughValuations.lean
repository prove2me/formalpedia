-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P20.localizable_iff_enoughValuations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T07:25:04.238673+00:00
-- url     : https://prove2.me/submissions/e4ac8c1d-3289-4144-baeb-8ddb71a3176f

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

open QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

theorem g67c_restrict {A : Type u} [CompleteBooleanAlgebra A] (nu : A → ℝ≥0)
    (hnu : IsPositiveContinuousValuation nu) (a : A) :
    IsPositiveContinuousValuation (fun x : Set.Iic a => nu x.val) := by
  obtain ⟨⟨hbot, hmod⟩, hmono, hcont⟩ := hnu
  refine ⟨⟨hbot, fun x y => hmod x.val y.val⟩, fun x y hxy => hmono hxy, ?_⟩
  intro s b hsne hdir hlub
  have hl : IsLUB (Subtype.val '' s) b.val := by
    constructor
    · rintro _ ⟨x, hx, rfl⟩; exact hlub.1 hx
    · intro u hu
      have : b ≤ ⟨u ⊓ a, inf_le_right⟩ := hlub.2 (fun x hx =>
        show x.val ≤ u ⊓ a from le_inf (hu ⟨x, hx, rfl⟩) x.2)
      exact (show b.val ≤ u ⊓ a from this).trans inf_le_left
  have hd : DirectedOn (· ≤ ·) (Subtype.val '' s) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
    exact ⟨z.val, ⟨z, hz, rfl⟩, hxz, hyz⟩
  have h := hcont _ _ (hsne.image _) hd hl
  rw [Set.image_image] at h
  exact h

theorem g67c_extend {A : Type u} [CompleteBooleanAlgebra A] (a : A) (mu : Set.Iic a → ℝ≥0)
    (hmu : IsPositiveContinuousValuation mu) :
    IsPositiveContinuousValuation (fun x : A => mu ⟨x ⊓ a, inf_le_right⟩) := by
  obtain ⟨⟨hbot, hmod⟩, hmono, hcont⟩ := hmu
  refine ⟨⟨?_, fun x y => ?_⟩, fun x y hxy => hmono (show x ⊓ a ≤ y ⊓ a from inf_le_inf_right a hxy), ?_⟩
  · have : (⟨(⊥ : A) ⊓ a, inf_le_right⟩ : Set.Iic a) = ⊥ := Subtype.ext (by simp)
    simp only; rw [this, hbot]
  · have h1 : (⟨(x ⊔ y) ⊓ a, inf_le_right⟩ : Set.Iic a) =
        (⟨x ⊓ a, inf_le_right⟩ : Set.Iic a) ⊔ ⟨y ⊓ a, inf_le_right⟩ :=
      Subtype.ext (by
        show (x ⊔ y) ⊓ a = (x ⊓ a) ⊔ (y ⊓ a)
        rw [inf_sup_right])
    have h2 : (⟨(x ⊓ y) ⊓ a, inf_le_right⟩ : Set.Iic a) =
        (⟨x ⊓ a, inf_le_right⟩ : Set.Iic a) ⊓ ⟨y ⊓ a, inf_le_right⟩ :=
      Subtype.ext (by
        show (x ⊓ y) ⊓ a = (x ⊓ a) ⊓ (y ⊓ a)
        rw [inf_inf_distrib_right])
    simp only; rw [h1, h2]; exact hmod _ _
  · intro s b hsne hdir hlub
    let g : A → Set.Iic a := fun x => ⟨x ⊓ a, inf_le_right⟩
    have hb : b = sSup s := hlub.unique (isLUB_sSup s)
    have hl : IsLUB (g '' s) (g b) := by
      constructor
      · rintro _ ⟨x, hx, rfl⟩
        exact show x ⊓ a ≤ b ⊓ a from inf_le_inf_right a (hlub.1 hx)
      · intro u hu
        show b ⊓ a ≤ u.val
        rw [hb, sSup_inf_eq]
        exact iSup₂_le fun x hx => (show g x ≤ u from hu ⟨x, hx, rfl⟩)
    have hd : DirectedOn (· ≤ ·) (g '' s) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
      exact ⟨g z, ⟨z, hz, rfl⟩, show x ⊓ a ≤ z ⊓ a from inf_le_inf_right a hxz,
        show y ⊓ a ≤ z ⊓ a from inf_le_inf_right a hyz⟩
    have h := hcont _ _ (hsne.image _) hd hl
    rw [Set.image_image] at h
    exact h

theorem solution (A : Type u) [CompleteBooleanAlgebra A] :
    HasFiniteValuationCover A ↔ ∀ b : A, b ≠ ⊥ →
      ∃ nu : A → ℝ≥0, IsPositiveContinuousValuation nu ∧ nu b ≠ 0 := by
  constructor
  · intro hcov b hb
    have : ∃ g ∈ {a : A | ∃ nu : Set.Iic a → ℝ≥0,
        IsPositiveContinuousValuation nu ∧ ∀ b, nu b = 0 → b = ⊥}, b ⊓ g ≠ ⊥ := by
      by_contra hall
      push Not at hall
      apply hb
      have : b = b ⊓ ⊤ := (inf_top_eq b).symm
      rw [this, ← hcov, inf_sSup_eq]
      exact le_antisymm (iSup₂_le fun d hd => (hall d hd).le) bot_le
    obtain ⟨g, ⟨mu, hmu, hfaith⟩, hbg⟩ := this
    refine ⟨_, g67c_extend g mu hmu, fun h0 => hbg ?_⟩
    have := hfaith _ h0
    exact congrArg Subtype.val this
  · intro h
    unfold HasFiniteValuationCover
    set G := {a : A | ∃ nu : Set.Iic a → ℝ≥0,
        IsPositiveContinuousValuation nu ∧ ∀ b, nu b = 0 → b = ⊥}
    set g := sSup G
    by_contra hne
    have hgc : gᶜ ≠ ⊥ := fun h' => hne (compl_eq_bot.1 h')
    obtain ⟨nu, hnu, hnz⟩ := h gᶜ hgc
    have hnu' := hnu
    obtain ⟨⟨hbot, hmod⟩, hmono, hcont⟩ := hnu'
    let Z : Set A := {x | nu x = 0}
    set n := sSup Z
    have hsupz : ∀ x y, x ∈ Z → y ∈ Z → x ⊔ y ∈ Z := by
      intro x y hx hy
      have := hmod x y
      simp only [Z, Set.mem_setOf_eq] at hx hy ⊢
      rw [hx, hy, zero_add] at this
      exact (add_eq_zero.1 this.symm).1
    have hn : nu n = 0 := by
      have hc := hcont Z n ⟨⊥, hbot⟩
        (fun x hx y hy => ⟨x ⊔ y, hsupz x y hx hy, le_sup_left, le_sup_right⟩) (isLUB_sSup Z)
      exact le_antisymm (hc.2 (by rintro _ ⟨x, hx, rfl⟩; exact le_of_eq hx)) bot_le
    set c := gᶜ ⊓ nᶜ
    have hcG : c ∈ G := by
      refine ⟨fun x => nu x.val, g67c_restrict nu hnu c, fun x hx => ?_⟩
      apply Subtype.ext
      have hxn : x.val ≤ n := le_sSup hx
      have hxc : x.val ≤ nᶜ := x.2.trans inf_le_right
      show x.val = ⊥
      exact le_antisymm (le_inf hxn hxc |>.trans (inf_compl_self n).le) bot_le
    have hcle : c ≤ g := le_sSup hcG
    have hc0 : c = ⊥ := le_antisymm ((le_inf hcle inf_le_left).trans (inf_compl_self g).le) bot_le
    apply hnz
    have h1 : gᶜ ≤ c ⊔ n := by
      rw [sup_comm, sup_inf_left, sup_compl_eq_top, inf_top_eq]; exact le_sup_right
    have h2 := hmono h1
    rw [hc0, bot_sup_eq, hn] at h2
    exact le_antisymm h2 bot_le
