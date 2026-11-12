-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12SelectedPortDensity_eq_resourceAcceptedMarginal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:29:51.587869+00:00
-- url     : https://prove2.me/submissions/9cc22caa-7c7f-4996-a5f0-eaa0df5ac5be

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12AcceptedOutput_eq_resourceAcceptedOutput
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_resourceAcceptedWeight_noisyResources_eq_rawSuccessMass


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
    (p : ErrorParameter) (hsuccess : 0 < rawSuccessMass q p) (port : OddRow q) :
    bh12SelectedPortDensity q p port =
      (bh12SelectedPortSubsystem q port).selectedPartialTraceFromRegister.mapDensity
        (resourceAcceptedOutput q (noisyResources q p)
          (by
            rw [resourceAcceptedWeight_noisyResources_eq_rawSuccessMass]
            exact hsuccess)) := by
  rw [bh12SelectedPortDensity, bh12AcceptedOutput_eq_resourceAcceptedOutput q p hsuccess]
end QEC.Distillation.Triorthogonal.BH12Concatenation
