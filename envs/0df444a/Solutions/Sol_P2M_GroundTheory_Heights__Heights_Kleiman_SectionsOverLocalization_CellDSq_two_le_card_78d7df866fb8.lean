-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_two_le_card_78d7df866fb8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:00.19091+00:00
-- url     : https://prove2.me/submissions/0ca97eb7-fd59-4f78-8ef6-c4107601bbb9

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
omit [Fintype K] [LinearOrder K]
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
theorem _root_.solution {I : ∀ k, Finset (ι k)} {k : K} {i : ι k} (hi : i ∈ I k)
    (h : ((I k).erase i).Nonempty) : 2 ≤ (I k).card := by
  have := h.card_pos
  rw [Finset.card_erase_of_mem hi] at this
  omega
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
