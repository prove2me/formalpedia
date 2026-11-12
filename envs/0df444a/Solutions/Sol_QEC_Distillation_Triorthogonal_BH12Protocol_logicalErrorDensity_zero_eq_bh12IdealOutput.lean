-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.logicalErrorDensity_zero_eq_bh12IdealOutput
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T19:41:42.80391+00:00
-- url     : https://prove2.me/submissions/8ae94057-e1ce-44ee-b505-46b40820b659

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
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

theorem solution (q : Nat) :
    logicalErrorDensity (0 : Word (ZMod 2) (OddRow q)) =
      bh12IdealOutput q := by
  apply DensityOperator.ext_toOperator
  rw [logicalErrorDensity_toOperator, logicalErrorState_zero,
    bh12IdealOutput, DensityOperator.pureDensity_toOperator]