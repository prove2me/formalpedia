-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PhysicalFlaggedBatch_total_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:32:31.496201+00:00
-- url     : https://prove2.me/submissions/4cdaae6d-d41a-4de9-bc01-4a6aa78909e8

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
theorem _root_.solution (q : Nat) (p : ErrorParameter) :
    ∑ error : PhysicalError q, (bh12PhysicalFlaggedBatch q p).weight error = 1 :=
  (bh12PhysicalFlaggedBatch q p).total_weight
end QEC.Distillation.Triorthogonal.BH12Concatenation
