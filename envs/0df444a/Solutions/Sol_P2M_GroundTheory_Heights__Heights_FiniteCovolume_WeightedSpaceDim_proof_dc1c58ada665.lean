-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedSpaceDim_proof_dc1c58ada665
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:06:28.303373+00:00
-- url     : https://prove2.me/submissions/21ac50ef-4ac8-472e-8d27-712f15433399

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PWeightedSpaceDim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField NumberField.InfinitePlace Module
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace WeightedSpaceDim
theorem _root_.solution (E : Type*) [Field E] [NumberField E] [IsTotallyComplex E] :
    WeightedSpaceDim.Statement E := by
  unfold WeightedSpaceDim.Statement
  rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin,
    card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero,
    IsTotallyComplex.finrank]
  ring
end WeightedSpaceDim
end GroundTheory.Heights₂.Heights.FiniteCovolume
