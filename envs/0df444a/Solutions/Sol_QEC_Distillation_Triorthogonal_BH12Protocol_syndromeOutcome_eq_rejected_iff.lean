-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.syndromeOutcome_eq_rejected_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T18:51:12.489484+00:00
-- url     : https://prove2.me/submissions/80dd8564-8980-42ef-a4f1-8c44a9dee6a1

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
    syndromeOutcome syndrome = .rejected ↔ syndrome ≠ trivialSyndrome := by
  simp [syndromeOutcome]