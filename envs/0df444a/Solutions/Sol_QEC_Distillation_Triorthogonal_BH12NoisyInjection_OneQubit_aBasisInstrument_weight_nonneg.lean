-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.aBasisInstrument_weight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:29:11.312602+00:00
-- url     : https://prove2.me/submissions/2f096256-da09-4740-be3c-d50ba911790c

import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_nonneg


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12NoisyInjection
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
open QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit
open Semantics.Qubit
open OneQubitMagic
namespace QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit
theorem _root_.solution (outcome : StabilizerOutcome)
    (rho : DensityOperator QubitSpace) :
    0 ≤ aBasisInstrument.bornWeight outcome rho :=
  aBasisInstrument.bornWeight_nonneg outcome rho
end QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit
