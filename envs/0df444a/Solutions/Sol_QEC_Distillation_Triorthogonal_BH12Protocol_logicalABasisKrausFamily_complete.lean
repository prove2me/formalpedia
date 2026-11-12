-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisKrausFamily_complete
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T19:38:56.705908+00:00
-- url     : https://prove2.me/submissions/54af7098-fb42-4e41-97ec-3116dc162116

import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_logicalABasisProjector_add
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_logicalABasisProjector_adjoint
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_logicalABasisProjector_idempotent
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
    (logicalABasisKrausFamily a).Complete := by
  unfold FiniteKrausFamily.Complete
  simp only [logicalABasisKrausFamily, logicalABasisProjector_adjoint]
  change
    (∑ outcome : StabilizerOutcome,
      logicalABasisProjector a outcome * logicalABasisProjector a outcome) = 1
  rw [show (Finset.univ : Finset StabilizerOutcome) =
      {.positive, .negative} by decide]
  simpa [logicalABasisProjector_idempotent] using
    logicalABasisProjector_add a