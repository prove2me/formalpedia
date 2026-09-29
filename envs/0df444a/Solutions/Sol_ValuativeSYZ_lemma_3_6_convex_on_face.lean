-- Prove2me | solution 1 for ValuativeSYZ.lemma_3_6_convex_on_face
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T18:34:52.847426+00:00
-- url     : https://prove2.me/submissions/f8c7eae0-9ae3-4240-ada5-4cef329a1cdd

import Mathlib
import Definitions.Def_ValuativeSYZ_cost_transform
import Definitions.Def_ValuativeSYZ_degeneration

/-! 7a4f9f9a ValuativeSYZ.lemma_3_6_convex_on_face: every function of the class P_c is
convex on a convex set on which each c(·, p) is convex. Writing φ = ψᶜ with ψ bounded, the
family p ↦ c x p - ψ p is bounded above by M + M'; for each p, convexity of c(·, p) and
ψ p = a ψ p + b ψ p give c(ax+by) p - ψ p ≤ a φ(x) + b φ(y), and ciSup_le finishes.
No `Theorems.*` module is imported. -/

set_option autoImplicit false

open MeasureTheory ValuativeSYZ in
theorem solution {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nonempty B] (c : E → B → ℝ) (M : ℝ) (hc : ∀ x p, |c x p| ≤ M)
    (s : Set E) (hs : Convex ℝ s) (hconv : ∀ p, ConvexOn ℝ s fun x => c x p)
    (φ : E → ℝ) (hφ : φ ∈ Pc c) : ConvexOn ℝ s φ := by
  obtain ⟨ψ, ⟨M', hM'⟩, rfl⟩ := hφ
  have hbdd : ∀ x, BddAbove (Set.range fun p => c x p - ψ p) := by
    intro x
    refine ⟨M + M', ?_⟩
    rintro _ ⟨p, rfl⟩
    have h1 := (abs_le.mp (hc x p)).2
    have h2 := (abs_le.mp (hM' p)).1
    show c x p - ψ p ≤ M + M'
    linarith
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  show (⨆ p, (c (a • x + b • y) p - ψ p)) ≤
      a • (⨆ p, (c x p - ψ p)) + b • (⨆ p, (c y p - ψ p))
  refine ciSup_le fun p => ?_
  have hcv := (hconv p).2 hx hy ha hb hab
  simp only [smul_eq_mul] at hcv ⊢
  have hx' : c x p - ψ p ≤ ⨆ q, (c x q - ψ q) := le_ciSup (hbdd x) p
  have hy' : c y p - ψ p ≤ ⨆ q, (c y q - ψ q) := le_ciSup (hbdd y) p
  have e : c (a • x + b • y) p - ψ p = c (a • x + b • y) p - (a * ψ p + b * ψ p) := by
    rw [← add_mul, hab, one_mul]
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hx' ha, mul_le_mul_of_nonneg_left hy' hb]
