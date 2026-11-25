-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_numStandardTable_eq_frobDim_2ce7df01df95
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:30:57.659134+00:00
-- url     : https://prove2.me/submissions/f5544a5b-26ba-4cc0-9779-9c12a8497257

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltFrob
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PLemmaC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (h1 : FrobeniusDimensionFormula.Statement) {m : ℕ}
    (lam : Fin m → ℕ) (hlam : Antitone lam) :
    (numStandardTable lam : ℚ) = GroundTheory.Heights₂.Heights.frobDim lam := by
  rw [h1 m lam hlam, GroundTheory.Heights₂.Heights.frobDim]
  congr 2
  unfold vandermondeOf
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]
end GroundTheory.Heights₂.Heights.RestTerms
