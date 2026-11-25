-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_mCoordIdeal_genPt_4a2d546de20c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:05:47.101676+00:00
-- url     : https://prove2.me/submissions/3e2c3429-b431-481e-a480-0716d22ecd7a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualCurvePoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_mConeMap_eq_eval__a0f62726315a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_aeval_eq_zero_of_mem_3ac1f31f332f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_aeval_genPt_da9742bcf082
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveComplexPoint_eval__smul_homog_35af9e8e8d54


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
variable {B : Type} [Fintype B] {ι : B → Type} [∀ k, Fintype (ι k)]
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.DualCurvePointAlt
theorem _root_.solution (W : Ideal (MRing ι)) [W.IsPrime] (hW : IsMultiHomogIdeal W) :
    mCoordIdeal (IndefiniteRowSideFullHecke.Inter.genPt W) = W := by
  refine le_antisymm (fun f hf => ?_) ?_
  · rw [← IndefiniteRowSideFullHecke.Inter.ker_algebraMap_comp_mk W, RingHom.mem_ker, RingHom.comp_apply, ← aeval_genPt]
    exact aeval_eq_zero_of_mem hf
  · obtain ⟨S, hS, hSW⟩ := hW
    calc W = Ideal.span S := hSW
      _ ≤ _ := Ideal.span_le.2 fun s hs => by
        obtain ⟨a, ha⟩ := hS s hs
        have hsW : s ∈ W := hSW ▸ Ideal.subset_span hs
        have h0 : eval₂ (Int.castRingHom _) (IndefiniteRowSideFullHecke.Inter.genPt W) s = 0 := by
          rw [aeval_genPt, Ideal.Quotient.eq_zero_iff_mem.2 hsW, map_zero]
        show s ∈ RingHom.ker _
        rw [RingHom.mem_ker, mConeMap_eq_eval₂]
        have h3 := IndefiniteRowSideFullHecke.HeightsSet.CurveComplexPoint.eval₂_smul_homog s a ha
          (fun k => (X k : MvPolynomial B (IndefiniteRowSideFullHecke.Inter.FnField W))) (fun p => C (IndefiniteRowSideFullHecke.Inter.genPt W p))
        have e2 : eval₂ (Int.castRingHom (MvPolynomial B (IndefiniteRowSideFullHecke.Inter.FnField W)))
            (fun p => C (IndefiniteRowSideFullHecke.Inter.genPt W p)) s =
              C (eval₂ (Int.castRingHom _) (IndefiniteRowSideFullHecke.Inter.genPt W) s) := by
          rw [eval₂_comp_left]
          congr 1
        have h4 : eval₂ (Int.castRingHom (MvPolynomial B (IndefiniteRowSideFullHecke.Inter.FnField W)))
            (fun p => C (IndefiniteRowSideFullHecke.Inter.genPt W p) * X p.1) s = 0 := by
          rw [show (fun p : Σ k, ι k => C (IndefiniteRowSideFullHecke.Inter.genPt W p) * X p.1) =
            fun p => X p.1 * C (IndefiniteRowSideFullHecke.Inter.genPt W p) from funext fun _ => mul_comm _ _, h3, e2, h0, C_0,
            mul_zero]
        exact h4
end GroundTheory.Heights₂.Heights.DualCurvePointAlt
