-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathSchedule_targetError_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:36:50.07487+00:00
-- url     : https://prove2.me/submissions/4b1b499c-76d7-4b64-bccd-efe2d8b6f1ea

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12QuadraticEnvelope_pos

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
    (hp : 0 < p.rate) (index : BH12PathScheduleIndex q) :
    0 < bh12PathScheduleTargetError q p index :=
  bh12QuadraticEnvelope_pos q p hp index.depth
end QEC.Distillation.Triorthogonal.BH12Concatenation
