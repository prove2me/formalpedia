-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.depthTwoChildSelectedPortTransportedDensity_eq_selectedPortDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:44:56.554281+00:00
-- url     : https://prove2.me/submissions/458d8612-d603-4cf6-a0f1-a5b327fc3379

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_depthTwoChildRun_eq_bh12ActualRun

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology
namespace QEC.Distillation.Triorthogonal.BH12Concatenation
theorem _root_.solution
    (q : Nat) (p : ErrorParameter) (hsuccess : 0 < rawSuccessMass q p)
    (firstPort secondPort : OddRow q) :
    depthTwoChildSelectedPortTransportedDensity q p firstPort secondPort =
      bh12SelectedPortTransportedDensity q
        (bh12DecodedMarginalErrorParameter q p hsuccess firstPort) secondPort := by
  unfold depthTwoChildSelectedPortTransportedDensity
  rw [depthTwoChildRun_eq_bh12ActualRun q p hsuccess firstPort]
  rfl
end QEC.Distillation.Triorthogonal.BH12Concatenation
