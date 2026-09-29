-- Prove2me | solution 1 for ValuativeSYZ.lemma_3_6_uniform_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T18:39:52.916732+00:00
-- url     : https://prove2.me/submissions/94e4f41e-f9d0-40a4-8308-0991ced1cd52

import Mathlib
import Definitions.Def_ValuativeSYZ_cost_transform
import Definitions.Def_ValuativeSYZ_degeneration

set_option autoImplicit false

open MeasureTheory

open ValuativeSYZ in
theorem solution {X B : Type*} [PseudoMetricSpace X] [Nonempty B]
    (c : X → B → ℝ) (Kc : NNReal) (M : ℝ)
    (hc : ∀ x p, |c x p| ≤ M) (hlip : ∀ p, LipschitzWith Kc fun x => c x p)
    (φ : X → ℝ) (hφ : φ ∈ Pc c) : LipschitzWith Kc φ := by
  obtain ⟨ψ, ⟨Mψ, hψ⟩, rfl⟩ := hφ
  have hbdd : ∀ x, BddAbove (Set.range fun p => c x p - ψ p) := fun x =>
    ⟨M + Mψ, by
      rintro _ ⟨p, rfl⟩
      have h1 := (abs_le.mp (hc x p)).2
      have h2 := (abs_le.mp (hψ p)).1
      simp only
      linarith⟩
  refine LipschitzWith.of_le_add_mul Kc fun x y => ?_
  unfold ctransformDual
  refine ciSup_le fun p => ?_
  have h := (hlip p).le_add_mul x y
  have h2 : c y p - ψ p ≤ ⨆ q, (c y q - ψ q) := le_ciSup (hbdd y) p
  linarith
