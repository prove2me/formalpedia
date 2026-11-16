-- Prove2me | solution 1 for TwoOptAllExp.TSP.Supplement.lemma_17
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T03:14:27.396505+00:00
-- url     : https://prove2.me/submissions/c9213883-fd5f-496c-b9ce-bdb4844fcc5f

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Supplement_GraphObjective
namespace TwoOptAllExp.TSP.Supplement.L17
open TwoOptAllExp.TSP.Supplement

variable {V : Type} [Fintype V] [DecidableEq V] (W : WGraph V)

lemma Δ_formula (x : V) (σ : V → Bool) :
    W.Δ x σ = W.b x + ∑ u ∈ W.G.neighborFinset x, W.w s(x, u) * (1 - 2 * b2i (σ u)) := by
  unfold WGraph.Δ WGraph.Φ
  have hv : ∑ v, W.b v * b2i (Function.update σ x true v) -
      ∑ v, W.b v * b2i (Function.update σ x false v) = W.b x := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single x]
    · simp [b2i]
    · intro v _ hv; simp [Function.update_of_ne hv]
    · simp
  have he : ∑ e ∈ W.G.edgeFinset, W.w e * WGraph.cut (Function.update σ x true) e -
      ∑ e ∈ W.G.edgeFinset, W.w e * WGraph.cut (Function.update σ x false) e =
      ∑ u ∈ W.G.neighborFinset x, W.w s(x, u) * (1 - 2 * b2i (σ u)) := by
    rw [← Finset.sum_sub_distrib]
    have h1 : ∑ e ∈ W.G.edgeFinset, (W.w e * WGraph.cut (Function.update σ x true) e -
        W.w e * WGraph.cut (Function.update σ x false) e) =
        ∑ e ∈ W.G.incidenceFinset x, (W.w e * WGraph.cut (Function.update σ x true) e -
        W.w e * WGraph.cut (Function.update σ x false) e) := by
      rw [SimpleGraph.incidenceFinset_eq_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e he
      split_ifs with hx
      · rfl
      · induction e using Sym2.ind with
        | h a b =>
          have ha : a ≠ x := fun h => hx (h ▸ Sym2.mem_mk_left _ _)
          have hb : b ≠ x := fun h => hx (h ▸ Sym2.mem_mk_right _ _)
          simp [WGraph.cut, Function.update_of_ne ha, Function.update_of_ne hb]
    rw [h1]
    have himg : W.G.incidenceFinset x = (W.G.neighborFinset x).image (fun u => s(x, u)) := by
      ext e
      simp only [SimpleGraph.mem_incidenceFinset, Finset.mem_image, SimpleGraph.mem_neighborFinset]
      constructor
      · intro he
        rcases he with ⟨he, hxe⟩
        obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp hxe
        exact ⟨u, by simpa using he, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨by simpa using hu, Sym2.mem_mk_left _ _⟩
    rw [himg, Finset.sum_image (fun a _ b _ h => Sym2.congr_right.mp h)]
    apply Finset.sum_congr rfl
    intro u hu
    rw [SimpleGraph.mem_neighborFinset] at hu
    have hux : u ≠ x := (W.G.ne_of_adj hu).symm
    simp only [WGraph.cut, Sym2.lift_mk, Function.update_self, Function.update_of_ne hux]
    cases σ u <;> simp [b2i]
  linarith [hv, he]



lemma Δ3 (z x y : V) (t : Option V) (hxy : x ≠ y) (htx : t ≠ some x) (hty : t ≠ some y)
    (hnbr : ∀ u : V, W.G.Adj z u ↔ (u = x ∨ u = y ∨ t = some u)) (σ : V → Bool) :
    W.Δ z σ = W.b z + W.w s(z, x) * (1 - 2 * b2i (σ x)) + W.w s(z, y) * (1 - 2 * b2i (σ y))
      + W.tieTerm z t σ := by
  rw [Δ_formula]
  have hN : W.G.neighborFinset z = insert x (insert y t.toFinset) := by
    ext u; simp only [SimpleGraph.mem_neighborFinset, hnbr, Finset.mem_insert, Option.mem_toFinset,
      Option.mem_def]
  have hx : x ∉ insert y t.toFinset := by
    simp only [Finset.mem_insert, Option.mem_toFinset, Option.mem_def, not_or]; exact ⟨hxy, htx⟩
  have hy : y ∉ t.toFinset := by simpa using hty
  rw [hN, Finset.sum_insert hx, Finset.sum_insert hy]
  cases t with
  | none => simp [WGraph.tieTerm]; ring
  | some t₀ => simp [WGraph.tieTerm]; ring

theorem main (D : ℤ) (hD : 0 < D)
    (z x y : V) (t : Option V) (hxy : x ≠ y) (htx : t ≠ some x) (hty : t ≠ some y)
    (hnbr : ∀ u : V, W.G.Adj z u ↔ (u = x ∨ u = y ∨ t = some u))
    (hr : ∀ σ : V → Bool, |W.tieTerm z t σ| < D) : 
    (W.w s(z, x) = -D → W.w s(z, y) = D → W.b z = -D →
      (∀ σ : V → Bool,
        W.Δ z σ = 2 * D * (b2i (σ x) - b2i (σ y)) - D + W.tieTerm z t σ ∧
        ((σ x = true ∧ σ y = false) → W.Δ z σ = D + W.tieTerm z t σ) ∧
        (¬ (σ x = true ∧ σ y = false) → W.Δ z σ ≤ -D + W.tieTerm z t σ)) ∧
      W.Follows z (fun σ => σ x && !σ y)) ∧
    (W.w s(z, x) = -D → W.w s(z, y) = -D → W.b z = D →
      (∀ σ : V → Bool,
        W.Δ z σ = 2 * D * (b2i (σ x) + b2i (σ y)) - D + W.tieTerm z t σ) ∧
      W.Follows z (fun σ => σ x || σ y)) ∧
    (∀ t₀ : V, t = some t₀ → W.w s(z, x) = -D → W.w s(z, y) = -D → W.b z = 0 →
      (∀ σ : V → Bool,
        W.Δ z σ = 2 * D * (b2i (σ x) + b2i (σ y) - 1) + W.tieTerm z t σ) ∧
      W.FollowsOn z (fun σ => σ x) {σ | σ x = σ y} ∧
      (0 < W.w s(z, t₀) → W.FollowsOn z (fun σ => !σ t₀) {σ | σ x ≠ σ y}) ∧
      (W.w s(z, t₀) < 0 → W.FollowsOn z (fun σ => σ t₀) {σ | σ x ≠ σ y})) := by
  have hΔ := Δ3 W z x y t hxy htx hty hnbr
  refine ⟨fun h1 h2 h3 => ?_, fun h1 h2 h3 => ?_, fun t₀ ht h1 h2 h3 => ?_⟩
  · have key : ∀ σ : V → Bool, W.Δ z σ = 2 * D * (b2i (σ x) - b2i (σ y)) - D + W.tieTerm z t σ := by
      intro σ; rw [hΔ, h1, h2, h3]; ring
    refine ⟨fun σ => ⟨key σ, ?_, ?_⟩, ?_⟩
    · rintro ⟨a, b⟩; rw [key, a, b]; simp [b2i]; ring
    · intro hn; rw [key]
      cases a : σ x <;> cases b : σ y <;> simp_all [b2i] <;> linarith
    · intro σ _
      have hr' := abs_lt.mp (hr σ)
      rw [key]
      cases a : σ x <;> cases b : σ y <;> simp [b2i, a, b] <;> (try constructor) <;> (try intro) <;> linarith
  · have key : ∀ σ : V → Bool, W.Δ z σ = 2 * D * (b2i (σ x) + b2i (σ y)) - D + W.tieTerm z t σ := by
      intro σ; rw [hΔ, h1, h2, h3]; ring
    refine ⟨key, ?_⟩
    intro σ _
    have hr' := abs_lt.mp (hr σ)
    rw [key]
    cases a : σ x <;> cases b : σ y <;> simp [b2i, a, b] <;> (try constructor) <;> (try intro) <;> linarith
  · have key : ∀ σ : V → Bool, W.Δ z σ = 2 * D * (b2i (σ x) + b2i (σ y) - 1) + W.tieTerm z t σ := by
      intro σ; rw [hΔ, h1, h2, h3]; ring
    refine ⟨key, ?_, ?_, ?_⟩
    · intro σ hσ
      have hr' := abs_lt.mp (hr σ)
      simp only [Set.mem_setOf_eq] at hσ
      rw [key, ← hσ]
      cases a : σ x <;> simp [b2i, a] <;> (try constructor) <;> (try intro) <;> linarith
    · intro hw σ hσ
      simp only [Set.mem_setOf_eq] at hσ
      have e : b2i (σ x) + b2i (σ y) - 1 = 0 := by
        cases a : σ x <;> cases b : σ y <;> simp_all [b2i]
      rw [key, e, ht]; simp only [WGraph.tieTerm]
      cases c : σ t₀ <;> simp [b2i, c] <;> (try constructor) <;> (try intro) <;> linarith
    · intro hw σ hσ
      simp only [Set.mem_setOf_eq] at hσ
      have e : b2i (σ x) + b2i (σ y) - 1 = 0 := by
        cases a : σ x <;> cases b : σ y <;> simp_all [b2i]
      rw [key, e, ht]; simp only [WGraph.tieTerm]
      cases c : σ t₀ <;> simp [b2i, c] <;> (try constructor) <;> (try intro) <;> linarith

end TwoOptAllExp.TSP.Supplement.L17

namespace TwoOptAllExp.TSP.Supplement

theorem lemma_17 {V : Type} [Fintype V] [DecidableEq V] (W : WGraph V) (D : ℤ) (hD : 0 < D)
    (z x y : V) (t : Option V) (hxy : x ≠ y) (htx : t ≠ some x) (hty : t ≠ some y)
    (hnbr : ∀ u : V, W.G.Adj z u ↔ (u = x ∨ u = y ∨ t = some u))
    (hr : ∀ σ : V → Bool, |W.tieTerm z t σ| < D) :
    (W.w s(z, x) = -D → W.w s(z, y) = D → W.b z = -D →
      (∀ σ : V → Bool,
        W.Δ z σ = 2 * D * (b2i (σ x) - b2i (σ y)) - D + W.tieTerm z t σ ∧
        ((σ x = true ∧ σ y = false) → W.Δ z σ = D + W.tieTerm z t σ) ∧
        (¬ (σ x = true ∧ σ y = false) → W.Δ z σ ≤ -D + W.tieTerm z t σ)) ∧
      W.Follows z (fun σ => σ x && !σ y)) ∧
    (W.w s(z, x) = -D → W.w s(z, y) = -D → W.b z = D →
      (∀ σ : V → Bool,
        W.Δ z σ = 2 * D * (b2i (σ x) + b2i (σ y)) - D + W.tieTerm z t σ) ∧
      W.Follows z (fun σ => σ x || σ y)) ∧
    (∀ t₀ : V, t = some t₀ → W.w s(z, x) = -D → W.w s(z, y) = -D → W.b z = 0 →
      (∀ σ : V → Bool,
        W.Δ z σ = 2 * D * (b2i (σ x) + b2i (σ y) - 1) + W.tieTerm z t σ) ∧
      W.FollowsOn z (fun σ => σ x) {σ | σ x = σ y} ∧
      (0 < W.w s(z, t₀) → W.FollowsOn z (fun σ => !σ t₀) {σ | σ x ≠ σ y}) ∧
      (W.w s(z, t₀) < 0 → W.FollowsOn z (fun σ => σ t₀) {σ | σ x ≠ σ y})) :=
  L17.main W D hD z x y t hxy htx hty hnbr hr

end TwoOptAllExp.TSP.Supplement

open TwoOptAllExp.TSP.Supplement in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (W : WGraph V) (D : ℤ) (hD : 0 < D)
    (z x y : V) (t : Option V) (hxy : x ≠ y) (htx : t ≠ some x) (hty : t ≠ some y)
    (hnbr : ∀ u : V, W.G.Adj z u ↔ (u = x ∨ u = y ∨ t = some u))
    (hr : ∀ σ : V → Bool, |W.tieTerm z t σ| < D) :
    (W.w s(z, x) = -D → W.w s(z, y) = D → W.b z = -D →
      (∀ σ : V → Bool,
        W.Δ z σ = 2 * D * (b2i (σ x) - b2i (σ y)) - D + W.tieTerm z t σ ∧
        ((σ x = true ∧ σ y = false) → W.Δ z σ = D + W.tieTerm z t σ) ∧
        (¬ (σ x = true ∧ σ y = false) → W.Δ z σ ≤ -D + W.tieTerm z t σ)) ∧
      W.Follows z (fun σ => σ x && !σ y)) ∧
    (W.w s(z, x) = -D → W.w s(z, y) = -D → W.b z = D →
      (∀ σ : V → Bool,
        W.Δ z σ = 2 * D * (b2i (σ x) + b2i (σ y)) - D + W.tieTerm z t σ) ∧
      W.Follows z (fun σ => σ x || σ y)) ∧
    (∀ t₀ : V, t = some t₀ → W.w s(z, x) = -D → W.w s(z, y) = -D → W.b z = 0 →
      (∀ σ : V → Bool,
        W.Δ z σ = 2 * D * (b2i (σ x) + b2i (σ y) - 1) + W.tieTerm z t σ) ∧
      W.FollowsOn z (fun σ => σ x) {σ | σ x = σ y} ∧
      (0 < W.w s(z, t₀) → W.FollowsOn z (fun σ => !σ t₀) {σ | σ x ≠ σ y}) ∧
      (W.w s(z, t₀) < 0 → W.FollowsOn z (fun σ => σ t₀) {σ | σ x ≠ σ y})) :=
  TwoOptAllExp.TSP.Supplement.lemma_17 W D hD z x y t hxy htx hty hnbr hr
