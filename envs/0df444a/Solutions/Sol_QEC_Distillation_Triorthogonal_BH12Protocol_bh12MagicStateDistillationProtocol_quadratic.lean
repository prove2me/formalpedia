-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.bh12MagicStateDistillationProtocol_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:17:58.03431+00:00
-- url     : https://prove2.me/submissions/2fd6ac9c-a49a-4b32-9c77-762d290b9a36

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_decodedMarginalError_le_evenFamily_quadratic
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_bh12MagicStateDistillationProtocol_successfulOutputError

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
namespace QEC.Distillation.Triorthogonal.BH12Protocol
theorem _root_.solution (q : Nat)
    (p : ErrorParameter) (a : OddRow q) (hhalf : p.rate ≤ 1 / 2) :
    (bh12MagicStateDistillationProtocol q p a
      (rawSuccessMass_pos_of_rate_le_half q p hhalf)).successfulOutputError ≤
      8 * ((1 + 6 * q : Nat) : ℝ) * p.rate ^ 2 := by
  rw [bh12MagicStateDistillationProtocol_successfulOutputError]
  exact decodedMarginalError_le_evenFamily_quadratic q p a hhalf
end QEC.Distillation.Triorthogonal.BH12Protocol
