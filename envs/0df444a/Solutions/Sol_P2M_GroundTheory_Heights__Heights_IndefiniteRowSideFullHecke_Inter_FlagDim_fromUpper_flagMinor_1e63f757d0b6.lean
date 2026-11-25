-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_fromUpper_flagMinor_1e63f757d0b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:33:01.609258+00:00
-- url     : https://prove2.me/submissions/6a84426e-f096-45fa-ab75-f1c58b9ba852

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_flagMinor_map_a36e9c2a7a1b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_reduce_lower_297a6269eea0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_reduce_diag_9c120aecada3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_flagMinor_lowerUni_mul_0fed1b5723b1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_fromUpper_uMat_8539412649be

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
variable (F : Type) [Field F] (n : ℕ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
theorem _root_.solution (j : Fin (n - 1)) (S : PluckerBlocks n n j) :
    fromUpper F n (flagMinor (uMat F n) j S) =
      algebraMap _ (GenField F n) (flagMinor (genMat F n) j S) := by
  have hj := j.2
  have e1 : fromUpper F n (flagMinor (uMat F n) j S) =
      flagMinor ((uMat F n).map (fromUpper F n).toRingHom) j S := (flagMinor_map _ _ _ _).symm
  rw [e1, ← flagMinor_map]
  have : flagMinor ((uMat F n).map (fromUpper F n).toRingHom) j S = flagMinor (genRed F n) j S := by
    simp only [flagMinor]
    congr 1
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.map_apply]
    exact fromUpper_uMat F n _ _ (by simp only [Fin.val_castLE]; omega)
  rw [this, genRed, flagMinor_lowerUni_mul _ _ (reduce_lower _) (reduce_diag _)]
  rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
