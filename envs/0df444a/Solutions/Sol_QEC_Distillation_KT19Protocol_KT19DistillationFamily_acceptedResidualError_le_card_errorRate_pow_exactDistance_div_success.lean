-- Prove2me | solution 1 for QEC.Distillation.KT19Protocol.KT19DistillationFamily.acceptedResidualError_le_card_errorRate_pow_exactDistance_div_success
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T14:45:18.8301+00:00
-- url     : https://prove2.me/submissions/bdadd5ec-7c7c-4580-a26a-04bdae97a080

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
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_success_pos_of_errorRate_lt_one
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_acceptedResidualMass_le_card_errorRate_pow_exactDistance

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
open QEC.Distillation.KT19Protocol.KT19DistillationFamily
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
namespace QEC.Distillation.KT19Protocol.KT19DistillationFamily
theorem _root_.solution
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (heps : kt19ErrorRate mu < 1) :
    acceptedResidualError family mu hmu_nonneg hmu_sum ≤
      ((Fintype.card (Word (ZMod p) (KeptPunctureLocation p k)) : ℝ) *
        kt19ErrorRate mu ^ (l + 1 - k)) /
        kt19Success family.rowFamily mu hmu_nonneg hmu_sum := by
  unfold acceptedResidualError
  exact div_le_div_of_nonneg_right
    (acceptedResidualMass_le_card_errorRate_pow_exactDistance
      family mu hmu_nonneg hmu_sum)
    (le_of_lt (success_pos_of_errorRate_lt_one
      family mu hmu_nonneg hmu_sum heps))
end QEC.Distillation.KT19Protocol.KT19DistillationFamily
