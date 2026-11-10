-- Prove2me | solution 1 for QEC.Distillation.KT19Protocol.kt19Run_raw_convex_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T14:37:42.880254+00:00
-- url     : https://prove2.me/submissions/b48501bd-6cf6-411c-886d-62b05a981dd4

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
import Theorems.Thm_QEC_Distillation_DistillationRun_rawOutput_eq_outcomeMixture


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
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    (kt19Run R mu hmu_nonneg hmu_sum).rawOutput =
      outcomeMixture (kt19Run R mu hmu_nonneg hmu_sum).successProbability
        (kt19Run R mu hmu_nonneg hmu_sum).success_nonneg
        (kt19Run R mu hmu_nonneg hmu_sum).success_le_one
        (kt19Run R mu hmu_nonneg hmu_sum).acceptedOutput
        (kt19Run R mu hmu_nonneg hmu_sum).rejectedOutput :=
  (kt19Run R mu hmu_nonneg hmu_sum).rawOutput_eq_outcomeMixture
end QEC.Distillation.KT19Protocol
