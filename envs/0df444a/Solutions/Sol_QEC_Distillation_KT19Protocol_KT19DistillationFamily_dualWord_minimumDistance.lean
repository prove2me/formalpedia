-- Prove2me | solution 1 for QEC.Distillation.KT19Protocol.KT19DistillationFamily.dualWord_minimumDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T14:35:25.515795+00:00
-- url     : https://prove2.me/submissions/5f737a16-d6b5-4451-8166-32158f7eafcc

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
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_dualWordCarrier_eq_punctured
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_puncturedComplementaryReedSolomon_minimumDistance


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
    (family : KT19DistillationFamily p l k) :
    MinimumDistance (kt19StabilizerCode family.rowFamily).dual (l + 1 - k) := by
  rcases puncturedComplementaryReedSolomon_minimumDistance p l k
    family.admissible with ⟨word, hword, hwordNe, hwordWeight, hleast⟩
  refine ⟨word, ?_, hwordNe, hwordWeight, ?_⟩
  · rw [dualWordCarrier_eq_punctured family]
    exact hword
  · intro candidate hcandidate hcandidateNe
    apply hleast candidate
    · rw [← dualWordCarrier_eq_punctured family]
      exact hcandidate
    · exact hcandidateNe
end QEC.Distillation.KT19Protocol.KT19DistillationFamily
