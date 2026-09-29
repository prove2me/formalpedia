-- Prove2me | solution 1 for ValuativeSYZ.lemma_3_5_biconjugate_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T18:29:19.620318+00:00
-- url     : https://prove2.me/submissions/cab6f8a3-4f98-4516-bb70-c9ab5a1bd3e2

import Mathlib
import Definitions.Def_ValuativeSYZ_cost_transform
import Definitions.Def_ValuativeSYZ_degeneration

/-! 0d791b32 ValuativeSYZ.lemma_3_5_biconjugate_le: the double c-transform of a bounded
function is dominated by the function. For each p, c x p - φᶜ(p) ≤ φ x because
φᶜ(p) = sup_y (c y p - φ y) ≥ c x p - φ x (the family is bounded above by 2M);
taking the sup over p gives the claim. No `Theorems.*` module is imported. -/

set_option autoImplicit false

open MeasureTheory ValuativeSYZ in
theorem solution {X B : Type*} [Nonempty X] [Nonempty B]
    (c : X → B → ℝ) (φ : X → ℝ) (M : ℝ)
    (hc : ∀ x p, |c x p| ≤ M) (hφ : ∀ x, |φ x| ≤ M) (x : X) :
    ctransformDual c (ctransform c φ) x ≤ φ x := by
  unfold ctransformDual ctransform
  refine ciSup_le fun p => ?_
  have hbdd : BddAbove (Set.range fun y : X => c y p - φ y) := by
    refine ⟨M + M, ?_⟩
    rintro _ ⟨y, rfl⟩
    have h1 := (abs_le.mp (hc y p)).2
    have h2 := (abs_le.mp (hφ y)).1
    show c y p - φ y ≤ M + M
    linarith
  have := le_ciSup hbdd x
  linarith
