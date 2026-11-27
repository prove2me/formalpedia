-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.equicont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:22:55.798426+00:00
-- url     : https://prove2.me/submissions/3573db48-60d2-44e6-bbe4-ad9d1a079e37

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedFDerivSubApply
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_SliceAn
import Theorems.Thm_GlobalTheory_CompanionTheory_SchwartzBaire_baireSpace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped SchwartzMap NNReal
variable {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution {ι : Type} (T : ι → 𝓢(V, ℂ) →L[ℂ] 𝓢(V₁, ℂ)) (q : Seminorm ℂ 𝓢(V₁, ℂ)) (hq : Continuous q)
    (h : ∀ f, ∃ C, ∀ i, q (T i f) ≤ C) : ∃ p : Seminorm ℂ 𝓢(V, ℂ), Continuous p ∧ ∀ i f, q (T i f) ≤ p f := by
  haveI := GlobalTheory.CompanionTheory.SchwartzBaire.baireSpace (E := V) (F := ℂ)
  have hb : BddAbove (range fun i => q.comp (T i).toLinearMap) := by
    rw [Seminorm.bddAbove_range_iff]
    intro f
    obtain ⟨C, hC⟩ := h f
    exact ⟨C, by rintro _ ⟨i, rfl⟩; exact hC i⟩
  refine ⟨⨆ i, q.comp (T i).toLinearMap, ?_, fun i f => ?_⟩
  · rw [Seminorm.coe_iSup_eq hb]
    exact Seminorm.continuous_iSup (fun i => q.comp (T i).toLinearMap) (fun i => hq.comp (T i).continuous) hb
  exact (le_ciSup hb i : q.comp (T i).toLinearMap ≤ _) f
end PositivityTheory.ThKG.Loc.Bump
