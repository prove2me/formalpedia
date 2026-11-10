-- Prove2me | solution 1 for QEC.Distillation.KT19Protocol.kt19SuccessfulOutputCost_eq_shared_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T14:32:17.615211+00:00
-- url     : https://prove2.me/submissions/3b5b32fa-42c6-481d-affb-19e886aea4bf

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_P11CubicBridge
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Semantics_Instruments_Branches_BranchOperatorLinear
import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_Protocol

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19Protocol
open Semantics
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open QEC.Distillation.KT19P11ReedSolomonCubicBridge
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] QEC.Distillation.KT19Protocol.instKT19ProtocolClassicalDecidable
attribute [local instance] QEC.Distillation.KT19Protocol.instKT19ProtocolClassicalDecidable
universe u
variable (p : Nat) [NeZero p]
variable {Site : Type u} [Fintype Site] [DecidableEq Site]
variable {q : Nat} [NeZero q] [Fact q.Prime]
variable {Logical Stabilizer : Type u} [Fintype Logical] [Fintype Stabilizer]
namespace QEC.Distillation.KT19Protocol
theorem _root_.solution [Nonempty Logical]
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    kt19SuccessfulOutputCost R mu hmu_nonneg hmu_sum =
      (Fintype.card Site : ℝ) /
        ((Fintype.card Logical : ℝ) *
          kt19Success R mu hmu_nonneg hmu_sum) := by
  unfold kt19SuccessfulOutputCost DistillationProtocolFamily.successfulOutputCost
  unfold DistillationProtocolFamily.inputResourceCount kt19OverheadFamily
  change (Fintype.card Site : ℝ) /
      ((Fintype.card Logical : ℝ) *
        (kt19Run R mu hmu_nonneg hmu_sum).successProbability) = _
  rw [kt19Run_successProbability]
  rfl
end QEC.Distillation.KT19Protocol
