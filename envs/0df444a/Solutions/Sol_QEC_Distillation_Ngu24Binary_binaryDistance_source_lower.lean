-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryDistance_source_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:27:47.313556+00:00
-- url     : https://prove2.me/submissions/608ee4d8-36b5-4434-b283-156798ac20b2

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryDistance
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryParameters
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryDistance_source_integer_lower
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedExtension_trans
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256QuditDistanceBound_source_lower


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
    (f256GarciaStichtenothLength i : ℚ) / 5 - f256MultiplicationLogicalCount i ≤
      binaryDistance i := by
  have h : (f256QuditDistanceBound i : ℚ) ≤ binaryDistance i := by
    exact_mod_cast binaryDistance_source_integer_lower i
  exact (f256QuditDistanceBound_source_lower i).trans h
end QEC.Distillation.Ngu24Binary
