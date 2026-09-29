-- Prove2me | solution 1 for ValuativeSYZ.lemma_3_5_ctransform_nonexpansive
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T18:21:38.732487+00:00
-- url     : https://prove2.me/submissions/8f4a08f6-4d74-4b71-a771-7a8feb15e053

import Mathlib
import Definitions.Def_ValuativeSYZ_cost_transform
import Definitions.Def_ValuativeSYZ_degeneration

set_option autoImplicit false

open MeasureTheory

open ValuativeSYZ in
theorem solution {X B : Type*} [Nonempty X]
    (c : X → B → ℝ) (φ ψ : X → ℝ) (M E : ℝ)
    (hc : ∀ x p, |c x p| ≤ M) (hφ : ∀ x, |φ x| ≤ M) (hψ : ∀ x, |ψ x| ≤ M)
    (hE : ∀ x, |φ x - ψ x| ≤ E) (p : B) :
    |ctransform c φ p - ctransform c ψ p| ≤ E := by
  unfold ctransform
  have hb1 : BddAbove (Set.range fun x => c x p - φ x) := by
    refine ⟨M + M, ?_⟩
    rintro _ ⟨x, rfl⟩
    have h1 := abs_le.mp (hc x p)
    have h2 := abs_le.mp (hφ x)
    show c x p - φ x ≤ M + M
    linarith [h1.2, h2.1]
  have hb2 : BddAbove (Set.range fun x => c x p - ψ x) := by
    refine ⟨M + M, ?_⟩
    rintro _ ⟨x, rfl⟩
    have h1 := abs_le.mp (hc x p)
    have h2 := abs_le.mp (hψ x)
    show c x p - ψ x ≤ M + M
    linarith [h1.2, h2.1]
  have k1 : (⨆ x, (c x p - ψ x)) ≤ (⨆ x, (c x p - φ x)) + E := by
    refine ciSup_le fun x => ?_
    have h3 := le_ciSup hb1 x
    have h4 := abs_le.mp (hE x)
    linarith [h4.1, h4.2]
  have k2 : (⨆ x, (c x p - φ x)) ≤ (⨆ x, (c x p - ψ x)) + E := by
    refine ciSup_le fun x => ?_
    have h3 := le_ciSup hb2 x
    have h4 := abs_le.mp (hE x)
    linarith [h4.1, h4.2]
  rw [abs_le]
  constructor <;> linarith

#print axioms solution
