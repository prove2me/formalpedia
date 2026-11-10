-- Prove2me | solution 1 for QEC.Distillation.KT19Protocol.p11OutputWorstPortError_le_two_mul_card_mul_card_errorRate_pow_three_div_success
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T14:49:55.584966+00:00
-- url     : https://prove2.me/submissions/726143c7-1de3-4ca1-9372-f87f9c5fe876

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
import Theorems.Thm_QEC_Distillation_KT19Protocol_p11AcceptedResidualError_le_card_errorRate_pow_three_div_success
import Theorems.Thm_QEC_Distillation_KT19Protocol_p11OutputWorstPortError_le_two_mul_card_mul_residualError

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
attribute [local instance] QEC.Distillation.KT19Protocol.p11Prime
attribute [local instance] QEC.Distillation.KT19Protocol.p11NeZero
attribute [local instance] QEC.Distillation.KT19Protocol.p11Prime QEC.Distillation.KT19Protocol.p11NeZero
namespace QEC.Distillation.KT19Protocol
theorem _root_.solution
    (mu : ZMod 11 → ℝ) (hmu_nonneg : ∀ a : ZMod 11, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod 11, mu a = 1)
    (heps : kt19ErrorRate mu < 1) :
    kt19OutputWorstPortError
      ((kt19Run p11CubicRowFamily mu hmu_nonneg hmu_sum).acceptedOutput) ≤
      2 * (Fintype.card (PrimeQuditRegisterLabel 11 (Fin 2)) : ℝ) *
        (((Fintype.card (Word (ZMod 11) (KeptPunctureLocation 11 2)) : ℝ) *
          kt19ErrorRate mu ^ 3) /
          kt19Success p11CubicRowFamily mu hmu_nonneg hmu_sum) := by
  calc
    kt19OutputWorstPortError
        ((kt19Run p11CubicRowFamily mu hmu_nonneg hmu_sum).acceptedOutput) ≤
        2 * (Fintype.card (PrimeQuditRegisterLabel 11 (Fin 2)) : ℝ) *
          p11AcceptedResidualError mu hmu_nonneg hmu_sum :=
      p11OutputWorstPortError_le_two_mul_card_mul_residualError
        mu hmu_nonneg hmu_sum heps
    _ ≤ 2 * (Fintype.card (PrimeQuditRegisterLabel 11 (Fin 2)) : ℝ) *
          (((Fintype.card (Word (ZMod 11) (KeptPunctureLocation 11 2)) : ℝ) *
            kt19ErrorRate mu ^ 3) /
            kt19Success p11CubicRowFamily mu hmu_nonneg hmu_sum) := by
      exact mul_le_mul_of_nonneg_left
        (p11AcceptedResidualError_le_card_errorRate_pow_three_div_success
          mu hmu_nonneg hmu_sum heps)
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
end QEC.Distillation.KT19Protocol
