-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GrassmannianArithmeticVariety_colsOf_anchor_c9a4e51f2489
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:20.559449+00:00
-- url     : https://prove2.me/submissions/02aa9baf-6f3d-4b8c-b980-64cfb275d159

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassArithVar

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.GrassmannianArithmeticVariety
namespace GroundTheory.Heights₂.Heights.GrassmannianArithmeticVariety
theorem _root_.solution {R : Type*} [CommRing R] {j m : ℕ} (Z : Matrix (Fin j) (Fin m) R) :
    colsOf (onePipe Z) (plAnchor j m) = 1 := by
  have he : ((plAnchor j m).1.orderEmbOfFin (plAnchor j m).2 : Fin j → Fin (j + m)) =
      Fin.castAdd m :=
    (Finset.orderEmbOfFin_unique _ (fun x => by simp [plAnchor]) (Fin.strictMono_castAdd m)).symm
  ext r i
  simp [colsOf, onePipe, he]
end GroundTheory.Heights₂.Heights.GrassmannianArithmeticVariety
