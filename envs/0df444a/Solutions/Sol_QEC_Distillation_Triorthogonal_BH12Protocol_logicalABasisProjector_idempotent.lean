-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisProjector_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T19:36:09.679775+00:00
-- url     : https://prove2.me/submissions/a54b41f0-1a4e-45da-8d82-25265225a9ae

import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_logicalABasisObservable_square
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

theorem solution {q : Nat} (a : OddRow q)
    (outcome : StabilizerOutcome) :
    logicalABasisProjector a outcome * logicalABasisProjector a outcome =
      logicalABasisProjector a outcome := by
  cases outcome <;>
    simp only [logicalABasisProjector, StabilizerOutcome.sign,
      smul_mul_assoc, mul_smul_comm, mul_add, add_mul, one_mul, mul_one,
      logicalABasisObservable_square] <;>
    module