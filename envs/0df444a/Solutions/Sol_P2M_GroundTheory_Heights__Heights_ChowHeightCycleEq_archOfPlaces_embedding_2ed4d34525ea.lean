-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_archOfPlaces_embedding_2ed4d34525ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:29:23.906749+00:00
-- url     : https://prove2.me/submissions/d401e2d9-6921-409f-a5a5-6d0678b09624

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ArchOfPlacesEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ChowHeightCycleEq
variable {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChowHeightCycleEq
theorem _root_.solution {K : Type} [Field K] [NumberField K]
    (N : InfinitePlace K → HermNorm n)
    (hN : ∀ w : InfinitePlace K, w.IsReal → ∀ u, (N w).norm (star u) = (N w).norm u)
    (w : InfinitePlace K) : (archOfPlaces N hN).normAt w.embedding = N w := by
  simp [archOfPlaces, InfinitePlace.mk_embedding]
end GroundTheory.Heights₂.Heights.ChowHeightCycleEq
