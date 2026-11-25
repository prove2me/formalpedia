-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_isAlgebraic_uMat_d1e54cce0458
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:09:25.811522+00:00
-- url     : https://prove2.me/submissions/478a4210-e97b-42ce-9d07-430f7c6012a9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_toUpper_flagMinorMap_X_200458d87616
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_flagMinor_uMat_colSet_7757b14e6865
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_isAlgebraic_of_mul_eq_4708e16f6489
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_diagProd_ne_zero_7de1111daeff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_exists_diagProd_4ab7521a86a6

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
theorem _root_.solution (j : Fin (n - 1)) (c : Fin n) (hc : j.val ≤ c.val) :
    letI := (Ideal.kerLiftAlg ((toUpper F n).comp (flagMinorMap F n))).toRingHom.toAlgebra
    IsAlgebraic (UpperQuot F n) (uMat F n ⟨j.val, by omega⟩ c) := by
  let _ := (Ideal.kerLiftAlg ((toUpper F n).comp (flagMinorMap F n))).toRingHom.toAlgebra
  have hj := j.2
  obtain ⟨a, ha⟩ := exists_diagProd F n j
  refine isAlgebraic_of_mul_eq (a := a)
    (b := Ideal.Quotient.mk _ (X ⟨j, ⟨colSet j.val c, colSet_card j.val c hc⟩⟩)) ?_ ?_
  · intro h0
    rw [h0, map_zero] at ha
    exact diagProd_ne_zero F n j.val (by omega) ha.symm
  · change Ideal.kerLiftAlg _ a * _ = Ideal.kerLiftAlg _ _
    rw [ha, Ideal.kerLiftAlg_mk, toUpper_flagMinorMap_X]
    simp only
    rw [flagMinor_uMat_colSet F j c hc, diagProd]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
