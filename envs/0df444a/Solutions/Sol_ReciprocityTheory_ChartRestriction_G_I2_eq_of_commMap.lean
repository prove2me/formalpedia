-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.eq_of_commMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:11:09.647969+00:00
-- url     : https://prove2.me/submissions/ec917c1a-31b7-4f71-9bf8-53c68d09788e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (t t' : (E →+* ℂ) → ℂ) (ht : ConjSymm t) (ht' : ConjSymm t')
    (h : mixedEmbedding.commMap E t = mixedEmbedding.commMap E t') : t = t' := by
  funext σ
  obtain ⟨w, hwdef⟩ : ∃ w, w = InfinitePlace.mk σ := ⟨_, rfl⟩
  have hcases := InfinitePlace.embedding_mk_eq σ
  rw [← hwdef] at hcases
  have key : t w.embedding = t' w.embedding := by
    by_cases hw : w.IsReal
    · have h1 := congrArg (fun m => m.1 ⟨w, hw⟩) h
      simp only [mixedEmbedding.commMap_apply_of_isReal] at h1
      have hr : ComplexEmbedding.conjugate w.embedding = w.embedding :=
        ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hw)
      have a1 : starRingEnd ℂ (t w.embedding) = t w.embedding := by rw [← ht, hr]
      have a2 : starRingEnd ℂ (t' w.embedding) = t' w.embedding := by rw [← ht', hr]
      apply Complex.ext h1
      rw [Complex.conj_eq_iff_im.mp a1, Complex.conj_eq_iff_im.mp a2]
    · have hw' : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
      have h1 := congrArg (fun m => m.2 ⟨w, hw'⟩) h
      simpa only [mixedEmbedding.commMap_apply_of_isComplex] using h1
  rcases hcases with he | he
  · rw [he] at key
    exact key
  · rw [he, ht, ht'] at key
    simpa using congrArg (starRingEnd ℂ) key
end ReciprocityTheory.ChartRestriction.G.I2
