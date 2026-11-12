-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.aBasisTwirl_eq_dephasing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:30:14.578788+00:00
-- url     : https://prove2.me/submissions/4b351b24-7698-4db4-93fc-d1551a3f457f

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
theorem _root_.solution : aBasisTwirl = aBasisDephasing :=
  rfl
end QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit
