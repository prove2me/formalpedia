-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootPointConjugation_map_minor_86bd49ff7f1a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:14:44.42204+00:00
-- url     : https://prove2.me/submissions/7ef5b84f-1f06-4dd8-9ba7-fa3f789c1ffb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootPointConj

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
open GroundTheory.Heights₂.Heights.RootPointConjugation
namespace GroundTheory.Heights₂.Heights.RootPointConjugation
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {j m : ℕ}
    (Z : Matrix (Fin j) (Fin m) R) (I : PlIdx j m) :
    φ (colsOf (onePipe Z) I).det = (colsOf (onePipe (Z.map φ)) I).det := by
  rw [RingHom.map_det]
  congr 1
  ext r c
  simp only [RingHom.mapMatrix_apply, map_apply, colsOf, submatrix_apply, onePipe, of_apply, id]
  generalize I.1.orderEmbOfFin I.2 c = x
  refine Fin.addCases (fun c' => ?_) (fun b => ?_) x
  · simp only [Fin.append_left, one_apply]; split_ifs <;> simp
  · simp [Fin.append_right]
end GroundTheory.Heights₂.Heights.RootPointConjugation
