-- Prove2me | solution 1 for QEC.Distillation.KT19Protocol.kt19SuccessfulOutputCost_le_one_sub_errorRate_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T14:40:32.223207+00:00
-- url     : https://prove2.me/submissions/88039ab1-1bb5-433d-9a3f-6c6a5ee3dc59

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
import Theorems.Thm_QEC_Distillation_KT19Protocol_kt19SuccessfulOutputCost_eq_shared_formula
import Theorems.Thm_QEC_Distillation_KT19Protocol_kt19Success_ge_one_sub_errorRate_pow

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
    (hmu_sum : ∑ a : ZMod q, mu a = 1)
    (heps : kt19ErrorRate mu < 1) :
    kt19SuccessfulOutputCost R mu hmu_nonneg hmu_sum ≤
      (Fintype.card Site : ℝ) /
        ((Fintype.card Logical : ℝ) *
          (1 - kt19ErrorRate mu) ^ Fintype.card Site) := by
  have hlogical : 0 < (Fintype.card Logical : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hpower : 0 < (1 - kt19ErrorRate mu) ^ Fintype.card Site :=
    pow_pos (sub_pos.mpr heps) _
  have hdenominator :
      (Fintype.card Logical : ℝ) *
          (1 - kt19ErrorRate mu) ^ Fintype.card Site ≤
        (Fintype.card Logical : ℝ) * kt19Success R mu hmu_nonneg hmu_sum :=
    mul_le_mul_of_nonneg_left
      (kt19Success_ge_one_sub_errorRate_pow R mu hmu_nonneg hmu_sum) hlogical.le
  rw [kt19SuccessfulOutputCost_eq_shared_formula]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
    (mul_pos hlogical hpower) hdenominator
end QEC.Distillation.KT19Protocol
