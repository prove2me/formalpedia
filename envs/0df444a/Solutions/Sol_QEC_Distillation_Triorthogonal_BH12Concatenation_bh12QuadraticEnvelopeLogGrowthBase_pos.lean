-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12QuadraticEnvelopeLogGrowthBase_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:30:42.83434+00:00
-- url     : https://prove2.me/submissions/d384ab39-c2f1-44f4-b6d0-092aeb8e15e8

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology
namespace QEC.Distillation.Triorthogonal.BH12Concatenation
theorem _root_.solution (q : Nat) (p : ErrorParameter)
    (hp : 0 < p.rate) (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2) :
    0 < bh12QuadraticEnvelopeLogGrowthBase q p := by
  unfold bh12QuadraticEnvelopeLogGrowthBase
  apply neg_pos.mpr
  apply Real.log_neg
  · exact mul_pos (quadraticCoefficient_pos q) hp
  · exact hstrong.trans_lt (by norm_num)
end QEC.Distillation.Triorthogonal.BH12Concatenation
