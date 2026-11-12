-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12OneLevelProtocolFamily_successfulOutputError_le_targetError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:33:53.785294+00:00
-- url     : https://prove2.me/submissions/5e3b7cc5-bd5e-46be-8fbd-03d773c990a0

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_bh12MagicStateDistillationProtocol_quadratic


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology
namespace QEC.Distillation.Triorthogonal.BH12Concatenation
theorem _root_.solution
    (q : Nat) (p : ErrorParameter) (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    ((bh12OneLevelProtocolFamily q p hhalf).protocol port).successfulOutputError ≤
      quadraticCoefficient q * p.rate ^ 2 := by
  change (bh12MagicStateDistillationProtocol q p port
    (rawSuccessMass_pos_of_rate_le_half q p hhalf)).successfulOutputError ≤ _
  exact bh12MagicStateDistillationProtocol_quadratic q p port hhalf
end QEC.Distillation.Triorthogonal.BH12Concatenation
