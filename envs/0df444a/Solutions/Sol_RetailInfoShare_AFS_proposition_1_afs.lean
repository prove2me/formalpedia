-- Prove2me | solution 1 for RetailInfoShare.AFS.proposition_1_afs
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T14:19:43.259704+00:00
-- url     : https://prove2.me/submissions/87c868ca-615c-46b0-9390-9972bb09762f

import Mathlib
import Definitions.Def_RetailInfoShare_AFS_Model
import Theorems.Thm_RetailInfoShare_AFS_endpoint_noise_level
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open RetailInfoShare.AFS in
theorem solution (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ)
    (M : NoiseMatrix P.N) (hM : IsOptimalAFS Z M) :
    ∀ i j, M i j = 0 ∨ M i j = ⊤ := by
  intro i j
  by_contra h
  push Not at h
  obtain ⟨hAFS, Q, hQ, hmax⟩ := hM
  set η := M i j
  have hcol : setColumn M j η = M := by
    funext i' j'
    unfold setColumn
    split_ifs with hj
    · subst hj; exact hAFS i i' j'
    · rfl
  rw [← hcol] at hQ
  obtain ⟨η', -, Q', hQ', hlt⟩ := endpoint_noise_level P hP μ Z M hAFS j η h.1 h.2 Q hQ
  have hAFS' : IsAFS (setColumn M j η') := by
    intro i₁ i₂ j'
    unfold setColumn
    split_ifs
    · rfl
    · exact hAFS i₁ i₂ j'
  have := hmax _ hAFS' Q' hQ'
  linarith
