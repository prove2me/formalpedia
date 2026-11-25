-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_sigma_rem_783ced986bac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:56.713127+00:00
-- url     : https://prove2.me/submissions/d5ee1748-fb60-4df8-b88a-fecf5747423f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DoubleSumEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
noncomputable section
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
theorem _root_.solution (I : ∀ k, Finset (ι k)) (p : Σ k, ι k) :
    Finset.univ.sigma (rem I p) = (Finset.univ.sigma I).erase p := by
  obtain ⟨k₀, i₀⟩ := p
  ext ⟨k, i⟩
  simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_erase, rem]
  by_cases hk : k = k₀
  · subst hk
    simp [Finset.mem_erase]
  · rw [Function.update_of_ne hk]
    simp [hk]
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
