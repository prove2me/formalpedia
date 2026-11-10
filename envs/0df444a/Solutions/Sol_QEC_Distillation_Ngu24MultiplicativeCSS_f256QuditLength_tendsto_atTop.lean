-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.f256QuditLength_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:39:02.324199+00:00
-- url     : https://prove2.me/submissions/620a689f-f91a-446d-bb73-2768b67ef2b8

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureDistance
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureFamily
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothLength_tendsto_atTop


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry.F256GarciaStichtenoth Semantics
open Ngu24MultiplicativeCCZ
open Filter
open scoped BigOperators Topology
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_a61e848631_24
namespace QEC.Distillation.Ngu24MultiplicativeCSS
theorem _root_.solution : Tendsto f256QuditLength atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hn := (tendsto_atTop.1 f256GarciaStichtenothLength_tendsto_atTop) (2 * b)
  filter_upwards [hn] with i hi
  unfold f256QuditLength f256MultiplicationLogicalCount
  omega
end QEC.Distillation.Ngu24MultiplicativeCSS
