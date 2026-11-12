-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisNegativeWeight_logicalErrorDensity
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T19:44:30.048723+00:00
-- url     : https://prove2.me/submissions/804049a6-d401-4db1-bee1-0ccf503a4627

import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_logicalABasisInstrument_branch_negative_logicalErrorDensity
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

theorem solution {q : Nat}
    (a : OddRow q) (logical : Word (ZMod 2) (OddRow q)) :
    logicalABasisNegativeWeight a (logicalErrorDensity logical) =
      if logical a = 0 then 0 else 1 := by
  rw [logicalABasisNegativeWeight, FiniteInstrument.bornWeight,
    logicalABasisInstrument_branch_negative_logicalErrorDensity]
  by_cases hbit : logical a = 0
  · rw [if_pos hbit, if_pos hbit]
    norm_num
  · rw [if_neg hbit, if_neg hbit,
      (logicalErrorDensity logical).trace_one]
    norm_num