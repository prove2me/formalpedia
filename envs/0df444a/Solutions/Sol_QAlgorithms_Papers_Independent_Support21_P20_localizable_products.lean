-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P20.localizable_products
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T07:26:46.127949+00:00
-- url     : https://prove2.me/submissions/94ba5617-0f0c-40ab-9ef7-73d35b5307fe

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

theorem g67c_eval {I : Type u} {A : I → Type u} [∀ i, CompleteBooleanAlgebra (A i)] (i : I)
    (nu : A i → ℝ≥0) (hnu : IsPositiveContinuousValuation nu) :
    IsPositiveContinuousValuation (fun x : ((i : I) → A i) => nu (x i)) := by
  obtain ⟨⟨hbot, hmod⟩, hmono, hcont⟩ := hnu
  refine ⟨⟨hbot, fun x y => hmod (x i) (y i)⟩, fun x y hxy => hmono (hxy i), ?_⟩
  intro s b hsne hdir hlub
  have hb : b = sSup s := hlub.unique (isLUB_sSup s)
  have hl : IsLUB ((fun x : ((i : I) → A i) => x i) '' s) (b i) := by
    rw [hb, sSup_apply_eq_sSup_image]; exact isLUB_sSup _
  have hd : DirectedOn (· ≤ ·) ((fun x : ((i : I) → A i) => x i) '' s) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
    exact ⟨z i, ⟨z, hz, rfl⟩, hxz i, hyz i⟩
  have h := hcont _ _ (hsne.image _) hd hl
  rw [Set.image_image] at h
  exact h

theorem solution (I : Type u) (A : I → Type u)
    [∀ i, CompleteBooleanAlgebra (A i)] (hA : ∀ i, HasFiniteValuationCover (A i)) :
    HasFiniteValuationCover ((i : I) → A i) ∧
    (∀ i : I, PreservesSuprema (fun a : ((i : I) → A i) => a i)) ∧
    (∀ (B : Type u) [CompleteBooleanAlgebra B], HasFiniteValuationCover B →
      ∀ f : (i : I) → BoundedLatticeHom B (A i),
        (∀ i, PreservesSuprema (f i)) →
        ∃! g : BoundedLatticeHom B ((i : I) → A i),
          PreservesSuprema g ∧ ∀ i b, g b i = f i b) ∧
    (∀ (B : Type u) [BooleanAlgebra B] (f : (i : I) → BoundedLatticeHom B (A i)),
      ∃! g : BoundedLatticeHom B ((i : I) → A i), ∀ i b, g b i = f i b) := by
  classical
  have hpi : ∀ (B : Type u) [BooleanAlgebra B] (f : (i : I) → BoundedLatticeHom B (A i)),
      ∃! g : BoundedLatticeHom B ((i : I) → A i), ∀ i b, g b i = f i b := by
    intro B _ f
    refine ⟨{ toFun := fun b i => f i b
              map_sup' := fun a b => by funext i; simp
              map_inf' := fun a b => by funext i; simp
              map_top' := by funext i; simp
              map_bot' := by funext i; simp }, fun i b => rfl, ?_⟩
    intro g hg
    ext b i
    exact hg i b
  refine ⟨?_, ?_, ?_, hpi⟩
  · unfold HasFiniteValuationCover
    rw [eq_top_iff]
    intro i
    show (⊤ : A i) ≤ (sSup _ : (j : I) → A j) i
    rw [sSup_apply_eq_sSup_image, ← hA i]
    apply sSup_le_sSup
    rintro a ⟨mu, hmu, hfaith⟩
    refine ⟨Function.update (⊥ : (j : I) → A j) i a, ?_, by simp⟩
    refine ⟨fun x => (fun y : ((j : I) → A j) => mu ⟨y i ⊓ a, inf_le_right⟩) x.val,
      g67c_restrict _ (g67c_eval i _ (g67c_extend a mu hmu)) _, fun x hx => ?_⟩
    have h0 := congrArg Subtype.val (hfaith _ hx)
    have hxi : x.val i ≤ a := by
      have := x.2 i; simpa using this
    apply Subtype.ext
    funext j
    show x.val j = ⊥
    by_cases hj : j = i
    · subst hj
      have : x.val j ⊓ a = ⊥ := h0
      rwa [inf_eq_left.2 hxi] at this
    · have := x.2 j
      rw [Function.update_of_ne hj] at this
      exact le_antisymm this bot_le
  · intro i s
    exact sSup_apply_eq_sSup_image
  · intro B _ _ f hf
    obtain ⟨g, hg, hu⟩ := hpi B f
    refine ⟨g, ⟨?_, hg⟩, fun g' hg' => hu g' hg'.2⟩
    intro s
    funext i
    rw [hg, hf i, sSup_apply_eq_sSup_image, Set.image_image]
    congr 1
    ext y
    simp [hg]
