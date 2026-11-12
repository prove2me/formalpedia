-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12QuadraticEnvelopeCostCoefficient_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:35:36.986453+00:00
-- url     : https://prove2.me/submissions/cc232aa8-4fa6-46b5-8368-aab4035bc0a7

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12QuadraticEnvelopeLogGrowthBase_pos

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
    0 < bh12QuadraticEnvelopeCostCoefficient q p := by
  unfold bh12QuadraticEnvelopeCostCoefficient
  exact div_pos (by norm_num)
    (Real.rpow_pos_of_pos
      (bh12QuadraticEnvelopeLogGrowthBase_pos q p hp hstrong)
      (bh12BlockExponent q))
end QEC.Distillation.Triorthogonal.BH12Concatenation
