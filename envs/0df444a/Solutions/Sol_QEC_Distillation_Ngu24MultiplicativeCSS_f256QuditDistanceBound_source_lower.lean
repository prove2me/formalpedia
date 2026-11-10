-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.f256QuditDistanceBound_source_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:44:34.333216+00:00
-- url     : https://prove2.me/submissions/3b0d9475-ffee-4215-9d7e-44c52638ebe0

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureDistance
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureFamily
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothLength_two_hundred_forty_le


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry.F256GarciaStichtenoth Semantics
open Ngu24MultiplicativeCCZ
open Filter
open scoped BigOperators Topology
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_a61e848631_24
namespace QEC.Distillation.Ngu24MultiplicativeCSS
theorem _root_.solution (i : ℕ) :
    (f256GarciaStichtenothLength i : ℚ) / 5 - f256MultiplicationLogicalCount i ≤
      f256QuditDistanceBound i := by
  have hn := f256GarciaStichtenothLength_two_hundred_forty_le i
  have h : f256GarciaStichtenothLength i ≤
      5 * (f256QuditDistanceBound i + f256MultiplicationLogicalCount i) := by
    unfold f256QuditDistanceBound f256MultiplicationLogicalCount
    omega
  have hq := (show (f256GarciaStichtenothLength i : ℚ) ≤
      5 * (f256QuditDistanceBound i + f256MultiplicationLogicalCount i) by exact_mod_cast h)
  linarith
end QEC.Distillation.Ngu24MultiplicativeCSS
