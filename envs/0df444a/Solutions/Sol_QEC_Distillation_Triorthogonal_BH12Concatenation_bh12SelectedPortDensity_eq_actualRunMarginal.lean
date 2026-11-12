-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12SelectedPortDensity_eq_actualRunMarginal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:29:42.96623+00:00
-- url     : https://prove2.me/submissions/5806aa43-9ebf-46b7-b421-4fdcc42fc628

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
theorem _root_.solution (q : Nat)
    (p : ErrorParameter) (port : OddRow q) :
    bh12SelectedPortDensity q p port =
      (bh12SelectedPortSubsystem q port).selectedPartialTraceFromRegister.mapDensity
        ((resourceDecodedRun q (noisyResources q p)).acceptedOutput) := by
  rfl
end QEC.Distillation.Triorthogonal.BH12Concatenation
