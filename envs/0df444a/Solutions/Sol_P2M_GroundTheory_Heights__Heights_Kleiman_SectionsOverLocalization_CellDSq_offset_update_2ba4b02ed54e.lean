-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_offset_update_2ba4b02ed54e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:20.041678+00:00
-- url     : https://prove2.me/submissions/77ff9fdb-d024-46a3-a828-f63f0caffeff

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
omit [∀ k, LinearOrder (ι k)]
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
theorem _root_.solution (I : ∀ k, Finset (ι k)) (k : K) (X : Finset (ι k)) :
    ∑ l ∈ Finset.univ.filter (· < k), ((Function.update I k X l).card - 1) =
      ∑ l ∈ Finset.univ.filter (· < k), ((I l).card - 1) :=
  Finset.sum_congr rfl fun l hl => by
    rw [Function.update_of_ne (ne_of_lt (Finset.mem_filter.1 hl).2)]
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
