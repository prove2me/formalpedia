-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.aBasisTwirl_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:30:28.862491+00:00
-- url     : https://prove2.me/submissions/41cf534e-60bd-4b26-a3d3-908f100d05d1

import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_OneQubit_aBasisDephasing_apply

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
theorem _root_.solution (A : Operator QubitSpace) :
    aBasisTwirl A =
      (1 / 2 : Complex) •
        (A + aBasisObservable.comp (A.comp aBasisObservable)) :=
  aBasisDephasing_apply A
end QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit
