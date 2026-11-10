-- Prove2me | solution 1 for QEC.Distillation.KT19Protocol.kt19AcceptedOutputDistribution_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T14:34:59.346409+00:00
-- url     : https://prove2.me/submissions/446d6459-6188-43f3-a36f-ac2153245109

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
import Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_magicRegisterInstrument_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_bornWeight_eq_one


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
theorem _root_.solution
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1)
    (hpos : 0 < kt19EndpointWeight R mu hmu_nonneg hmu_sum .accepted) :
    ∑ label : PrimeQuditRegisterLabel q Logical,
      kt19AcceptedOutputDistribution R mu hmu_nonneg hmu_sum hpos label = 1 :=
  (magicRegisterInstrument q (Site := Logical)).sum_bornWeight_eq_one
    (magicRegisterInstrument_complete q (Site := Logical))
    ((kt19DecoderChannel R).mapDensity
      (kt19EndpointConditional R mu hmu_nonneg hmu_sum .accepted hpos))
end QEC.Distillation.KT19Protocol
