-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.aZeroDensity_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:29:32.531421+00:00
-- url     : https://prove2.me/submissions/4247cef2-bf0d-490c-8ad4-f4d72baaacbf

import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection

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
theorem _root_.solution :
    aZeroDensity.toOperator =
      (InnerProductSpace.rankOne Complex aZeroState aZeroState).toLinearMap := by
  rw [aZeroDensity, phaseStateDensity_toOperator]
  rfl
end QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit
