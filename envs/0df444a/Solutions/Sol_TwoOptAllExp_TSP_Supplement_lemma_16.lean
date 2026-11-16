-- Prove2me | solution 1 for TwoOptAllExp.TSP.Supplement.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T03:13:13.840442+00:00
-- url     : https://prove2.me/submissions/404067aa-4983-4078-892d-83426407edaa

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Supplement_GraphObjective
namespace TwoOptAllExp.TSP.Supplement.L16
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


/-- residual -/
def Rs (x y : V) (σ : V → Bool) : ℤ :=
  ∑ u ∈ (W.G.neighborFinset x).erase y, W.w s(x, u) * (1 - 2 * b2i (σ u))

lemma Δ_split (x y : V) (hxy : W.G.Adj x y) (σ : V → Bool) :
    W.Δ x σ = W.b x + W.w s(x, y) * (1 - 2 * b2i (σ y)) + Rs W x y σ := by
  rw [Δ_formula, Rs, ← Finset.add_sum_erase _ _ (by simpa using hxy)]
  ring

lemma term_abs (a : ℤ) (c : Bool) : |a * (1 - 2 * b2i c)| = |a| := by
  cases c <;> simp [b2i, abs_neg]

lemma Rs_bounds (x y : V) (σ : V → Bool) :
    -W.B x y ≤ Rs W x y σ ∧ Rs W x y σ ≤ W.B x y := by
  unfold Rs WGraph.B
  constructor
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum; intro u _
    have := neg_abs_le (W.w s(x, u) * (1 - 2 * b2i (σ u)))
    rw [term_abs] at this; exact this
  · apply Finset.sum_le_sum; intro u _
    have := le_abs_self (W.w s(x, u) * (1 - 2 * b2i (σ u)))
    rw [term_abs] at this; exact this

lemma Rs_update (x y : V) (σ : V → Bool) (c : Bool) :
    Rs W x y (Function.update σ y c) = Rs W x y σ := by
  unfold Rs
  apply Finset.sum_congr rfl; intro u hu
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hu)]

lemma Rs_hi (x y : V) (c : Bool) : ∃ σ : V → Bool, σ y = c ∧ Rs W x y σ = W.B x y := by
  refine ⟨Function.update (fun u => decide (W.w s(x, u) < 0)) y c, by simp, ?_⟩
  rw [Rs_update]; unfold Rs WGraph.B
  apply Finset.sum_congr rfl; intro u _
  by_cases h : W.w s(x, u) < 0
  · simp [h, b2i, abs_of_neg h]
  · simp [h, b2i, abs_of_nonneg (not_lt.mp h)]

lemma Rs_lo (x y : V) (c : Bool) : ∃ σ : V → Bool, σ y = c ∧ Rs W x y σ = -W.B x y := by
  refine ⟨Function.update (fun u => decide (0 ≤ W.w s(x, u))) y c, by simp, ?_⟩
  rw [Rs_update]; unfold Rs WGraph.B
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro u _
  by_cases h : 0 ≤ W.w s(x, u)
  · simp [h, b2i, abs_of_nonneg h]
  · simp [h, b2i, abs_of_neg (not_le.mp h)]

theorem main (x y : V) (hxy : W.G.Adj x y) :
    (W.Follows x (fun σ => σ y) ↔
      0 < W.b x - W.w s(x, y) - W.B x y ∧ W.b x + W.w s(x, y) + W.B x y < 0) ∧
    (W.Follows x (fun σ => !σ y) ↔
      0 < W.b x + W.w s(x, y) - W.B x y ∧ W.b x - W.w s(x, y) + W.B x y < 0) ∧
    (W.b x = 0 →
      (W.Follows x (fun σ => σ y) ↔ W.w s(x, y) < -W.B x y) ∧
      (W.Follows x (fun σ => !σ y) ↔ W.B x y < W.w s(x, y))) := by
  have hb : ∀ c : Bool, b2i c = if c then 1 else 0 := fun c => rfl
  have ha : (W.Follows x (fun σ => σ y) ↔
      0 < W.b x - W.w s(x, y) - W.B x y ∧ W.b x + W.w s(x, y) + W.B x y < 0) := by
    unfold WGraph.Follows WGraph.FollowsOn
    constructor
    · intro h
      obtain ⟨σ1, h1, r1⟩ := Rs_lo W x y true
      obtain ⟨σ2, h2, r2⟩ := Rs_hi W x y false
      have e1 := (h σ1 trivial).1 h1
      have e2 := (h σ2 trivial).2 h2
      rw [Δ_split W x y hxy, h1, r1] at e1
      rw [Δ_split W x y hxy, h2, r2] at e2
      simp [b2i] at e1 e2
      constructor <;> linarith
    · rintro ⟨h1, h2⟩ σ _
      have hR := Rs_bounds W x y σ
      rw [Δ_split W x y hxy]
      constructor
      · intro hs; have : σ y = true := hs
        rw [this]; simp [b2i]; linarith [hR.1]
      · intro hs; have : σ y = false := hs
        rw [this]; simp [b2i]; linarith [hR.2]
  have hn : (W.Follows x (fun σ => !σ y) ↔
      0 < W.b x + W.w s(x, y) - W.B x y ∧ W.b x - W.w s(x, y) + W.B x y < 0) := by
    unfold WGraph.Follows WGraph.FollowsOn
    constructor
    · intro h
      obtain ⟨σ1, h1, r1⟩ := Rs_lo W x y false
      obtain ⟨σ2, h2, r2⟩ := Rs_hi W x y true
      have e1 := (h σ1 trivial).1 (by simp [h1])
      have e2 := (h σ2 trivial).2 (by simp [h2])
      rw [Δ_split W x y hxy, h1, r1] at e1
      rw [Δ_split W x y hxy, h2, r2] at e2
      simp [b2i] at e1 e2
      constructor <;> linarith
    · rintro ⟨h1, h2⟩ σ _
      have hR := Rs_bounds W x y σ
      rw [Δ_split W x y hxy]
      constructor
      · intro hs; have : σ y = false := by simpa using hs
        rw [this]; simp [b2i]; linarith [hR.1]
      · intro hs; have : σ y = true := by simpa using hs
        rw [this]; simp [b2i]; linarith [hR.2]
  refine ⟨ha, hn, fun h0 => ⟨?_, ?_⟩⟩
  · rw [ha, h0]; constructor
    · rintro ⟨a, b⟩; linarith
    · intro a; constructor <;> linarith
  · rw [hn, h0]; constructor
    · rintro ⟨a, b⟩; linarith
    · intro a; constructor <;> linarith

end TwoOptAllExp.TSP.Supplement.L16

namespace TwoOptAllExp.TSP.Supplement

theorem lemma_16 {V : Type} [Fintype V] [DecidableEq V] (W : WGraph V) (x y : V)
    (hxy : W.G.Adj x y) :
    (W.Follows x (fun σ => σ y) ↔
      0 < W.b x - W.w s(x, y) - W.B x y ∧ W.b x + W.w s(x, y) + W.B x y < 0) ∧
    (W.Follows x (fun σ => !σ y) ↔
      0 < W.b x + W.w s(x, y) - W.B x y ∧ W.b x - W.w s(x, y) + W.B x y < 0) ∧
    (W.b x = 0 →
      (W.Follows x (fun σ => σ y) ↔ W.w s(x, y) < -W.B x y) ∧
      (W.Follows x (fun σ => !σ y) ↔ W.B x y < W.w s(x, y))) :=
  L16.main W x y hxy

end TwoOptAllExp.TSP.Supplement

open TwoOptAllExp.TSP.Supplement in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (W : WGraph V) (x y : V)
    (hxy : W.G.Adj x y) :
    (W.Follows x (fun σ => σ y) ↔
      0 < W.b x - W.w s(x, y) - W.B x y ∧ W.b x + W.w s(x, y) + W.B x y < 0) ∧
    (W.Follows x (fun σ => !σ y) ↔
      0 < W.b x + W.w s(x, y) - W.B x y ∧ W.b x - W.w s(x, y) + W.B x y < 0) ∧
    (W.b x = 0 →
      (W.Follows x (fun σ => σ y) ↔ W.w s(x, y) < -W.B x y) ∧
      (W.Follows x (fun σ => !σ y) ↔ W.B x y < W.w s(x, y))) :=
  TwoOptAllExp.TSP.Supplement.lemma_16 W x y hxy

