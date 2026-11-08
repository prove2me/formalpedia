-- Prove2me | solution 1 for TransitoryQueue.lemma_6_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:30:51.573197+00:00
-- url     : https://prove2.me/submissions/39fb3a6f-aad6-4fe8-9437-013dde1ef72d

import Mathlib
import Definitions.Def_TransitoryQueue_reflect

open TransitoryQueue in
theorem solution (f g : ℝ → ℝ) (δ : ℝ) (hfg : ∀ t : ℝ, 0 ≤ t → |f t - g t| ≤ δ)
    (hf : ∀ t : ℝ, 0 ≤ t → BddBelow (f '' Set.Icc 0 t)) (t : ℝ) (ht : 0 ≤ t) :
    |(⨅ u : Set.Icc (0 : ℝ) t, f u) - ⨅ u : Set.Icc (0 : ℝ) t, g u| ≤ δ ∧
      |reflect f t - reflect g t| ≤ 2 * δ := by
  haveI : Nonempty (Set.Icc (0 : ℝ) t) := ⟨⟨0, le_refl 0, ht⟩⟩
  obtain ⟨M, hM⟩ := hf t ht
  have hbf : BddBelow (Set.range fun u : Set.Icc (0 : ℝ) t => f u) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨u, rfl⟩
    exact hM ⟨u, u.2, rfl⟩
  have hbg : BddBelow (Set.range fun u : Set.Icc (0 : ℝ) t => g u) := by
    refine ⟨M - δ, ?_⟩
    rintro _ ⟨u, rfl⟩
    have h1 := hM ⟨u, u.2, rfl⟩
    have h2 := abs_le.mp (hfg u u.2.1)
    simp only
    linarith [h2.2]
  have h1 : (⨅ u : Set.Icc (0 : ℝ) t, f u) - δ ≤ ⨅ u : Set.Icc (0 : ℝ) t, g u := by
    apply le_ciInf
    intro u
    have h3 := ciInf_le hbf u
    have h4 := abs_le.mp (hfg u u.2.1)
    linarith [h4.1]
  have h2 : (⨅ u : Set.Icc (0 : ℝ) t, g u) - δ ≤ ⨅ u : Set.Icc (0 : ℝ) t, f u := by
    apply le_ciInf
    intro u
    have h3 := ciInf_le hbg u
    have h4 := abs_le.mp (hfg u u.2.1)
    linarith [h4.2]
  have hI : |(⨅ u : Set.Icc (0 : ℝ) t, f u) - ⨅ u : Set.Icc (0 : ℝ) t, g u| ≤ δ :=
    abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  refine ⟨hI, ?_⟩
  unfold reflect
  have h5 := abs_le.mp (hfg t ht)
  have h6 := abs_le.mp hI
  rw [abs_le]
  constructor <;> linarith [h5.1, h5.2, h6.1, h6.2]
