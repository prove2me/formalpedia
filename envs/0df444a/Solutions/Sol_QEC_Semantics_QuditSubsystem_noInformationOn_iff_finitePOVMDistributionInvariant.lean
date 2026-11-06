-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.noInformationOn_iff_finitePOVMDistributionInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:18:31.607259+00:00
-- url     : https://prove2.me/submissions/0b3c0bce-aeec-448b-9967-d0790b4539ed

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_implies_finitePOVMDistributionInvariant
import Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_of_carrier_eq_bot
import Theorems.Thm_QEC_Semantics_QuditSubsystem_finitePOVMDistributionInvariant_implies_noInformationOn_of_nonzero

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution
    (C : QuantumCode (Qudit.QuditRegister q)) (S : QuditSubsystem q) :
    NoInformationOn C S ↔ FinitePOVMDistributionInvariant.{u, v} C S := by
  constructor
  · exact noInformationOn_implies_finitePOVMDistributionInvariant C S
  · intro hDistribution
    by_cases hC : C.carrier = ⊥
    · exact noInformationOn_of_carrier_eq_bot C S hC
    · exact finitePOVMDistributionInvariant_implies_noInformationOn_of_nonzero C S hC
        hDistribution
end QEC.Semantics.QuditSubsystem
