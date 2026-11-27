-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualTopMetricChange_proof_a1cff1eff997
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:55:30.69861+00:00
-- url     : https://prove2.me/submissions/13d06e4f-6faf-4887-b608-38e66dcb8166

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ScaledExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLineSemipositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIntDomainDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ReMulOfPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualTopMetricChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TopDualMetricChange_weight_smooth_7497b1b6e65e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TopDualMetricChange_dualLine_eq_tensor_6d359bea9348
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TopDualMetricChange_ptsIntegral_neg_f3372bd7f2ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TopDualMetricChange_degree_withStdMetric_sub_d27e90f4ad26
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeTrdeg_proof_69ca55d428ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordConeArithVar_proof_c88814975c4f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithVar_proof_4a52428ded73
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualLineSemipositive_proof_e177cbc37e01
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotDegree_proof_9f64677a504a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntDomainDim_proof_5fd7126bc8a9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesCoordDet_proof_ac9076ebb338
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesCoordImage_proof_2f9651d0e040
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesDiagGram_proof_07411a99c86a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesExtendBasis_proof_8fa7f46600b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesFischer_proof_6025e973d824
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGenIndexDet_proof_45e3ad0c112c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGenIndexMono_proof_2040980b39c9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGenIndexPi_proof_f2bf82a31706
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGenIndexTrans_proof_111d4bda05c6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGramChange_proof_6298f237c421
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGramDetChange_proof_df546a43ec2c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGramFischerBound_proof_77ebd3f93538
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGramPosDef_proof_0c282fd0c601
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesIdealIndexPos_proof_03ee9467f9ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesIdealLatticeFG_proof_67d24ec7f127
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesIdealStdIndex_proof_6b977d9b42dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesIsLattice_proof_02d454bfaf2d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesLatticeBasis_proof_e1dc639893aa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesLineDegree_proof_b34aa47f42dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesProductFormula_proof_6195c6dfe57b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesProjIndexLower_proof_661cddecff79
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesProjLattice_proof_53be31fed3e1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotDegreeBound_proof_61110a0b3b52
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotGramLog_proof_a60af463d04d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotIndexLog_proof_09489f015433
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotIndexSplit_proof_7a44e3708281
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotIndex_proof_036f85ded6ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesStdIndexDet_proof_c110655293b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesStdPi_proof_8714a4784b4c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrthogonalLines_proof_7f624962ae33
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 NumberField
noncomputable section
open TopDualMetricChange
namespace GroundTheory.Heights₂.Heights
namespace DualTopMetricChange
theorem _root_.solution (hTel : TelescopeStatement) (hEnergy : DualMetricEnergy.Statement) :
    DualTopMetricChange.Statement := by
  intro K _ _ i F T _ _ b hb II hi hII
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have hP : IsArithVar (dualIdeal b) (n + 1) :=
    DualArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) K (n + 1) F T b hi
  have hT := hTel Unit (dualBlocks T) (II Unit (dualBlocks T)) (hII Unit (dualBlocks T)) (dualIdeal b) n
    (dualLine F.withStdMetric b hb) (weight F b hb) (weight_hom F b hb) hP
    (DualLineSemipositive.proof K (n + 1) F.withStdMetric T b hb).1 (weight_smooth F b hb)
  rw [← dualLine_eq_tensor F b hb] at hT
  have hw : weight F b hb = fun z =>
      -(Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) := by
    funext z; simp only [weight]; ring
  rw [hw] at hT
  simp only [ptsIntegral_neg, Finset.sum_neg_distrib, neg_neg] at hT
  have hE : ∑ k ∈ Finset.range (n + 1),
      ptsIntegral (dualIdeal b)
        (pot fun j : Fin n => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
        (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) =
      1 / 2 * (∑ σ : K →+* ℂ, Real.log (F.metric σ).det.re) *
        geomDeg (grassIdeal 1 1 (n + 1 - 1)) (fsMulti (plBlocks 1 1 (n + 1 - 1))) (1 * 1 * (n + 1 - 1)) :=
    hEnergy K (n + 1) F T b hb hi
  rw [degree_withStdMetric_sub F]
  linarith
end DualTopMetricChange
end GroundTheory.Heights₂.Heights
