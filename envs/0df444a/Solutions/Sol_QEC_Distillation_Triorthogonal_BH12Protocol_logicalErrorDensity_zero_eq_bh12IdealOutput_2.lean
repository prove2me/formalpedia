-- Prove2me | solution 2 for QEC.Distillation.Triorthogonal.BH12Protocol.logicalErrorDensity_zero_eq_bh12IdealOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:48:53.25443+00:00
-- url     : https://prove2.me/submissions/d8254941-83b0-4009-ad60-b593859423fd

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
namespace QEC.Distillation.Triorthogonal.BH12Protocol
theorem _root_.solution (q : Nat) :
    logicalErrorDensity (0 : Word (ZMod 2) (OddRow q)) =
      bh12IdealOutput q := by
  apply DensityOperator.ext_toOperator
  rw [logicalErrorDensity_toOperator, logicalErrorState_zero,
    bh12IdealOutput, DensityOperator.pureDensity_toOperator]
end QEC.Distillation.Triorthogonal.BH12Protocol
