-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.blk_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:44:26.522424+00:00
-- url     : https://prove2.me/submissions/04513e5b-b3c2-4608-b75a-89b43ff37878

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_ParAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW Matrix
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
variable {K : Type} [CommRing K] {M : ℕ}
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution (a b c d a' b' c' d' : K) (r s u w r' s' u' w' : Fin M → K) (U U' : Matrix (Fin M) (Fin M) K) :
    blk a b r c d s u w U * blk a' b' r' c' d' s' u' w' U' =
      blk (a * a' + b * c' + r ⬝ᵥ u') (a * b' + b * d' + r ⬝ᵥ w') (a • r' + b • s' + r ᵥ* U')
        (c * a' + d * c' + s ⬝ᵥ u') (c * b' + d * d' + s ⬝ᵥ w') (c • r' + d • s' + s ᵥ* U')
        (a' • u + c' • w + U *ᵥ u') (b' • u + d' • w + U *ᵥ w') (vecMulVec u r' + vecMulVec w s' + U * U') := by
  ext i j
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_succ, dotProduct, vecMul, mulVec, vecMulVec_apply, add_assoc, mul_comm]
end PositivityTheory.PlacePermOperatorBicommutantSpan
