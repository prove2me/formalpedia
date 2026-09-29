-- Prove2me | solution 1 for QFS.ref_cones_paper
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-06T19:59:08.21616+00:00
-- url     : https://prove2.me/submissions/774c0d0a-8d64-4c2f-88bf-a7efd6bdb322

import Definitions.Def_QFS_RefCones
import Definitions.Def_QFS_Translate
import Definitions.Def_QFS_Defs
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open Real Set Metric InnerProductGeometry

open QFS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Lemma 2.2 exactly as the source states it**, with the common apex angle `θ`
existentially quantified. The development's `QFS.ref_cones` pins `θ = ϑ/3`, which is
what the proof of Lemma 2.2 delivers and is therefore stronger. -/
theorem solution {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ π / 2 ∧
      ∃ S : Finset E, (∀ v ∈ S, ‖v‖ = 1) ∧
        ∀ Γ : Configuration E, IsBounded Γ ϑ →
          ∀ x : E, ∃ v ∈ S, doubleCone v θ ⊆ (Γ x).carrier := by
  obtain ⟨S, hS, hcov⟩ := ref_cones (E := E) hϑ hϑ'
  exact ⟨ϑ / 3, by positivity, by linarith [pi_pos], S, hS, hcov⟩
