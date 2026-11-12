-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.depthTwoChildInputSlot_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:30:24.130074+00:00
-- url     : https://prove2.me/submissions/3bda5097-f4b4-4555-a03e-8cfd171c0b7b

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_DependentBatch_childInputSlot_injective


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology
namespace QEC.Distillation.Triorthogonal.BH12Concatenation
theorem _root_.solution (q : Nat)
    (child : Fin (bh12OutputCount q)) :
    Function.Injective (depthTwoChildInputSlot q child) := by
  intro left right h
  apply DependentBatch.childInputSlot_injective child
  apply (depthTwoRouting q).injective
  exact h
end QEC.Distillation.Triorthogonal.BH12Concatenation
