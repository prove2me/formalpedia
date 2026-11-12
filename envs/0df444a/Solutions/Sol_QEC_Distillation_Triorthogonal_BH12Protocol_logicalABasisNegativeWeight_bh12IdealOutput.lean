-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisNegativeWeight_bh12IdealOutput
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T19:46:56.300571+00:00
-- url     : https://prove2.me/submissions/8ef06963-31f6-4df0-9f3e-f206b81e2db7

import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_logicalABasisNegativeWeight_logicalErrorDensity
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_logicalErrorDensity_zero_eq_bh12IdealOutput
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
    (a : OddRow q) :
    logicalABasisNegativeWeight a (bh12IdealOutput q) = 0 := by
  rw [← logicalErrorDensity_zero_eq_bh12IdealOutput q,
    logicalABasisNegativeWeight_logicalErrorDensity]
  simp