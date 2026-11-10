-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryLogicalCount_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:04:45.514187+00:00
-- url     : https://prove2.me/submissions/762f59d4-1e3e-415f-b50b-dec58b512d65

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryDistance
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryParameters
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
    (binaryLength i : ℚ) / 10240 ≤ f256MultiplicationLogicalCount i ∧
      (f256MultiplicationLogicalCount i : ℚ) ≤ binaryLength i := by
  have hn := f256GarciaStichtenothLength_two_hundred_forty_le i
  have hnat : binaryLength i ≤ 10240 * f256MultiplicationLogicalCount i ∧
      f256MultiplicationLogicalCount i ≤ binaryLength i := by
    unfold binaryLength f256QuditLength f256MultiplicationLogicalCount
    omega
  have hlow : (binaryLength i : ℚ) ≤ 10240 * f256MultiplicationLogicalCount i := by
    exact_mod_cast hnat.1
  refine ⟨by linarith, ?_⟩
  exact_mod_cast hnat.2
end QEC.Distillation.Ngu24Binary
