-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_numberField_coords_38ed536ee690
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:11:35.649692+00:00
-- url     : https://prove2.me/submissions/7aeec21b-df1d-477e-bab4-aa3f16e421f3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualCurvePoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_mCoordIdeal_genPt_4a2d546de20c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_algebraMap_injective_3841fd1427ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mCoordIdeal_ratioPtL_13ad74b72e74
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_X_mem_of_eq_zero_e9e44dbdbf54
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_isAlgebraic_ratio_a456e2cba585


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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualCurvePointAlt
namespace GroundTheory.Heights₂.Heights.DualCurvePointAlt
theorem _root_.solution {T : Type} [Fintype T] (W : Ideal (MRing (fun _ : Unit => T)))
    (hW : IsArithVar W 1) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (z : (Σ _ : Unit, T) → L) (t0 : T),
      z ⟨(), t0⟩ = 1 ∧ mCoordIdeal z = W := by
  have : W.IsPrime := hW.2.1.1
  have hinj : Function.Injective (algebraMap ℤ (IndefiniteRowSideFullHecke.Inter.FnField W)) := by
    have e : algebraMap ℤ (IndefiniteRowSideFullHecke.Inter.FnField W) =
        (algebraMap (MRing (fun _ : Unit => T) ⧸ W) (IndefiniteRowSideFullHecke.Inter.FnField W)).comp
          (algebraMap ℤ (MRing (fun _ : Unit => T) ⧸ W)) := RingHom.ext_int _ _
    rw [e, RingHom.coe_comp]
    exact (IsFractionRing.injective _ _).comp (CoordinateConeArithVar.algebraMap_injective W hW.2.2.1)
  have : CharZero (IndefiniteRowSideFullHecke.Inter.FnField W) := charZero_of_injective_algebraMap hinj
  have hy : mCoordIdeal (IndefiniteRowSideFullHecke.Inter.genPt W) = W := mCoordIdeal_genPt W hW.2.1.2.1
  have hP : IsArithVar (mCoordIdeal (IndefiniteRowSideFullHecke.Inter.genPt W)) 1 := by rw [hy]; exact hW
  obtain ⟨t0, ht0⟩ := hW.2.1.2.2 ()
  have hc : ∀ k, IndefiniteRowSideFullHecke.Inter.genPt W ⟨k, (fun _ : Unit => t0) k⟩ ≠ 0 := fun k h =>
    ht0 (by rw [← hy]; exact IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.X_mem_of_eq_zero h)
  have : Finite (coneRatios (IndefiniteRowSideFullHecke.Inter.genPt W) fun _ : Unit => t0) := (Set.finite_range _).to_subtype
  have : FiniteDimensional ℚ (CoordinateConeArithVar.ratioField (IndefiniteRowSideFullHecke.Inter.genPt W) fun _ => t0) :=
    IntermediateField.finiteDimensional_adjoin fun x ⟨p, hp⟩ =>
      hp ▸ (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.isAlgebraic_ratio hP _ hc p).isIntegral
  have : CharZero (CoordinateConeArithVar.ratioField (IndefiniteRowSideFullHecke.Inter.genPt W) fun _ => t0) :=
    charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  refine ⟨CoordinateConeArithVar.ratioField (IndefiniteRowSideFullHecke.Inter.genPt W) fun _ => t0, inferInstance, ⟨⟩,
    CoordinateConeArithVar.ratioPtL (IndefiniteRowSideFullHecke.Inter.genPt W) fun _ => t0, t0, ?_, ?_⟩
  · apply Subtype.ext
    exact div_self (hc ())
  · rw [CoordinateConeArithVar.mCoordIdeal_ratioPtL _ _ hc, hy]
end GroundTheory.Heights₂.Heights.DualCurvePointAlt
