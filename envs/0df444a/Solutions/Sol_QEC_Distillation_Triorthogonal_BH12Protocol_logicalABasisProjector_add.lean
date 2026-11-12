-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisProjector_add
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T19:14:14.510033+00:00
-- url     : https://prove2.me/submissions/df6c3f77-979e-47ee-9cb9-fb27e83c36ed

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

theorem solution {q : Nat} (a : OddRow q) :
    logicalABasisProjector a .positive +
      logicalABasisProjector a .negative = 1 := by
  simp only [logicalABasisProjector, StabilizerOutcome.sign]
  module