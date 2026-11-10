-- Prove2me | solution 1 for QEC.Distillation.KT19Protocol.KT19DistillationFamily.acceptedWord_hammingWeight_ge_exactDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T14:37:40.09382+00:00
-- url     : https://prove2.me/submissions/287f1003-040f-46c5-bc75-a6aa5989c19a

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
import Theorems.Thm_QEC_Distillation_KT19Protocol_kt19AcceptedWord_iff_mem_stabilizerCode_dual
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_dualWord_minimumDistance

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
    (error : Word (ZMod p) (KeptPunctureLocation p k))
    (haccepted : kt19AcceptedWord family.rowFamily error) (herror : error ≠ 0) :
    l + 1 - k ≤ HammingWeight error := by
  have hacceptedDual :
      error ∈ (kt19StabilizerCode family.rowFamily).dual.carrier :=
    (kt19AcceptedWord_iff_mem_stabilizerCode_dual family.rowFamily error).mp haccepted
  rcases dualWord_minimumDistance family with
    ⟨word, hword, hwordNe, hwordWeight, hleast⟩
  exact hleast error hacceptedDual herror
end QEC.Distillation.KT19Protocol.KT19DistillationFamily
