-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12NoisyInjection.errorWordAmplitude_mul_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:31:32.685959+00:00
-- url     : https://prove2.me/submissions/f609a794-6b60-4a36-a4bf-e73e6afa7bab

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
variable {Index : Type u} [Fintype Index] [DecidableEq Index]
omit [DecidableEq Index]
namespace QEC.Distillation.Triorthogonal.BH12NoisyInjection
theorem _root_.solution (p : ErrorParameter)
    (error : Word (ZMod 2) Index) :
    errorWordAmplitude p error * star (errorWordAmplitude p error) =
      (errorWordProbability p error : Complex) := by
  rw [mul_comm, errorWordAmplitude_normSq]
end QEC.Distillation.Triorthogonal.BH12NoisyInjection
