-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_flagMinor_diagonal_mul_33770a16194e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:06:00.100668+00:00
-- url     : https://prove2.me/submissions/c66411f0-2604-42c3-b0c7-a8698999ff77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMultiHomog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
theorem _root_.solution {R : Type} [CommRing R] {n N1 : ℕ} (d : Fin n → R)
    (M : Matrix (Fin n) (Fin N1) R) (j : Fin (n - 1)) (T : PluckerBlocks N1 n j) :
    flagMinor (Matrix.diagonal d * M) j T =
      (∏ a : Fin (j.1 + 1), d ⟨a.1, by have := j.2; omega⟩) * flagMinor M j T := by
  unfold flagMinor
  rw [show (Matrix.diagonal d * M).submatrix (Fin.castLE (by have := j.2; omega)) (T.1.orderEmbOfFin T.2) =
      Matrix.diagonal (fun a : Fin (j.1 + 1) => d ⟨a.1, by have := j.2; omega⟩) *
        M.submatrix (Fin.castLE (by have := j.2; omega)) (T.1.orderEmbOfFin T.2) from by
    ext a b; simp [Matrix.diagonal_mul]; rfl, Matrix.det_mul, Matrix.det_diagonal]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
