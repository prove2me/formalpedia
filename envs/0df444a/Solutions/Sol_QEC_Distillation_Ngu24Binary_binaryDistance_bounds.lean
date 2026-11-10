-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryDistance_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:27:49.739136+00:00
-- url     : https://prove2.me/submissions/ee269fd9-9153-4d5d-b7d3-868dfe31aabc

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryDistance
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryParameters
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryDistance_source_integer_lower
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryDistance_le_length
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedExtension_trans
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothLength_two_hundred_forty_le


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter
open scoped BigOperators Topology
attribute [local instance] QEC.Distillation.Ngu24Binary._p2m_local_instance_6d70a6dbef_22
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (i : Nat) :
    (binaryLength i : ℚ) / 5120 ≤ binaryDistance i ∧
      (binaryDistance i : ℚ) ≤ binaryLength i := by
  have hn := f256GarciaStichtenothLength_two_hundred_forty_le i
  have hnat : binaryLength i ≤ 5120 * f256QuditDistanceBound i := by
    unfold binaryLength f256QuditLength f256QuditDistanceBound f256MultiplicationLogicalCount
    omega
  have hd := binaryDistance_source_integer_lower i
  have hlow : (binaryLength i : ℚ) ≤ 5120 * binaryDistance i := by
    exact_mod_cast hnat.trans (Nat.mul_le_mul_left 5120 hd)
  refine ⟨by linarith, ?_⟩
  exact_mod_cast binaryDistance_le_length i
end QEC.Distillation.Ngu24Binary
