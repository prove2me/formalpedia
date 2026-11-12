-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.syndromeOutcome_eq_accepted_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T18:56:41.324909+00:00
-- url     : https://prove2.me/submissions/c52ba593-7c00-4c84-a29c-746a2fc11f2c

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

theorem solution (syndrome : Syndrome) :
    syndromeOutcome syndrome = .accepted ↔ syndrome = trivialSyndrome := by
  simp [syndromeOutcome]