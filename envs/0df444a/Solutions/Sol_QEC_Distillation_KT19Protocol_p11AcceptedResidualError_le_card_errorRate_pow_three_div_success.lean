-- Prove2me | solution 1 for QEC.Distillation.KT19Protocol.p11AcceptedResidualError_le_card_errorRate_pow_three_div_success
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T14:43:28.30943+00:00
-- url     : https://prove2.me/submissions/d35e303b-3d48-45a0-8af4-e59c8687470b

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
import Theorems.Thm_QEC_Distillation_KT19Protocol_kt19Success_pos_of_errorRate_lt_one
import Theorems.Thm_QEC_Distillation_KT19Protocol_p11AcceptedResidualMass_le_card_errorRate_pow_three

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
    p11AcceptedResidualError mu hmu_nonneg hmu_sum ≤
      ((Fintype.card (Word (ZMod 11) (KeptPunctureLocation 11 2)) : ℝ) *
        kt19ErrorRate mu ^ 3) /
        kt19Success p11CubicRowFamily mu hmu_nonneg hmu_sum := by
  unfold p11AcceptedResidualError
  exact div_le_div_of_nonneg_right
    (p11AcceptedResidualMass_le_card_errorRate_pow_three mu hmu_nonneg hmu_sum)
    (le_of_lt (kt19Success_pos_of_errorRate_lt_one
      p11CubicRowFamily mu hmu_nonneg hmu_sum heps))
end QEC.Distillation.KT19Protocol
