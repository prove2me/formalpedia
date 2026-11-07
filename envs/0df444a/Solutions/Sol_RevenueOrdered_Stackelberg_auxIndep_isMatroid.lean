-- Prove2me | solution 1 for RevenueOrdered.Stackelberg.auxIndep_isMatroid
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T00:48:13.797845+00:00
-- url     : https://prove2.me/submissions/9a190ab5-fc49-4baa-8119-75e3f39eef06

import Mathlib
import Definitions.Def_RevenueOrdered_Stackelberg_Model
import Definitions.Def_RevenueOrdered_Stackelberg_Greedy
import Definitions.Def_RevenueOrdered_Stackelberg_Instance
import Definitions.Def_RevenueOrdered_Stackelberg_Assortment

open Classical

namespace StackG3Aux

open RevenueOrdered.Stackelberg

variable {α : Type*}

/-- The projection `R ∪ 𝒞 → E`, `a ↦ a`, `(e, q) ↦ e`. -/
def proj : α ⊕ (α × ℝ) → α := Sum.elim id Prod.fst

theorem mem_auxGround (I : Instance α) (x : α ⊕ (α × ℝ)) :
    x ∈ auxGround I ↔ (∃ a ∈ I.R, x = Sum.inl a) ∨
      (∃ e ∈ I.B, ∃ q ∈ costs I, x = Sum.inr (e, q)) := by
  unfold auxGround products
  rcases x with a | ⟨e, q⟩ <;> simp

theorem image_eq (I : Instance α) (X : Finset (α ⊕ (α × ℝ))) (hX : X ⊆ auxGround I) :
    proj '' (X : Set (α ⊕ (α × ℝ))) =
      (((I.R.filter (fun a => Sum.inl a ∈ X)) ∪
        (I.B.filter (fun e => ∃ q ∈ costs I, Sum.inr (e, q) ∈ X)) : Finset α) : Set α) := by
  ext a
  simp only [Set.mem_image, Finset.mem_coe, Finset.coe_union, Finset.coe_filter,
    Set.mem_union]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases (mem_auxGround I x).mp (hX hx) with ⟨b, hb, rfl⟩ | ⟨e, he, q, hq, rfl⟩
    · left; exact ⟨hb, hx⟩
    · right; exact ⟨he, q, hq, hx⟩
  · rintro (⟨ha, hx⟩ | ⟨ha, q, _, hx⟩)
    · exact ⟨_, hx, rfl⟩
    · exact ⟨_, hx, rfl⟩

theorem injOn_iff (I : Instance α) (X : Finset (α ⊕ (α × ℝ))) (hX : X ⊆ auxGround I) :
    Set.InjOn proj (X : Set (α ⊕ (α × ℝ))) ↔
      ∀ e ∈ I.B, (X.filter (fun y => ∃ q ∈ costs I, y = Sum.inr (e, q))).card ≤ 1 := by
  constructor
  · intro hinj e _
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Finset.mem_filter] at hx hy
    obtain ⟨q, _, rfl⟩ := hx.2
    obtain ⟨q', _, rfl⟩ := hy.2
    exact hinj (Finset.mem_coe.mpr hx.1) (Finset.mem_coe.mpr hy.1) rfl
  · intro hc x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    rcases (mem_auxGround I x).mp (hX hx) with ⟨a, ha, rfl⟩ | ⟨e, he, q, hq, rfl⟩ <;>
      rcases (mem_auxGround I y).mp (hX hy) with ⟨b, hb, rfl⟩ | ⟨e', he', q', hq', rfl⟩
    · simp only [proj, Sum.elim_inl, id] at hxy; rw [hxy]
    · simp only [proj, Sum.elim_inl, Sum.elim_inr, id] at hxy
      subst hxy
      exact absurd he' (Finset.disjoint_left.mp I.disjoint ha)
    · simp only [proj, Sum.elim_inl, Sum.elim_inr, id] at hxy
      subst hxy
      exact absurd hb (Finset.disjoint_right.mp I.disjoint he)
    · simp only [proj, Sum.elim_inr] at hxy
      subst hxy
      have := Finset.card_le_one.mp (hc e he) (Sum.inr (e, q))
        (Finset.mem_filter.mpr ⟨hx, q, hq, rfl⟩) (Sum.inr (e, q'))
        (Finset.mem_filter.mpr ⟨hy, q', hq', rfl⟩)
      exact this

end StackG3Aux

open RevenueOrdered.Stackelberg StackG3Aux in
theorem solution {α : Type*} (I : Instance α) :
    ∃ M' : Matroid (α ⊕ (α × ℝ)), M'.E = (auxGround I : Set (α ⊕ (α × ℝ))) ∧
      ∀ X : Finset (α ⊕ (α × ℝ)), M'.Indep (X : Set (α ⊕ (α × ℝ))) ↔ auxIndep I X := by
  refine ⟨Matroid.restrict (I.M.comap proj) (auxGround I : Set (α ⊕ (α × ℝ))), rfl, ?_⟩
  intro X
  rw [Matroid.restrict_indep_iff, Matroid.comap_indep_iff]
  unfold auxIndep
  constructor
  · rintro ⟨⟨hind, hinj⟩, hX⟩
    have hX' : X ⊆ auxGround I := by exact_mod_cast hX
    refine ⟨hX', (injOn_iff I X hX').mp hinj, ?_⟩
    rw [← image_eq I X hX']
    exact hind
  · rintro ⟨hX, hc, hind⟩
    refine ⟨⟨?_, (injOn_iff I X hX).mpr hc⟩, by exact_mod_cast hX⟩
    rw [image_eq I X hX]
    exact hind
