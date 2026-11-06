-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.noInformationOn_implies_finitePOVMDistributionInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:29:07.562239+00:00
-- url     : https://prove2.me/submissions/3cc60600-b172-450d-b8dc-7aebb5a7e2f8

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_trace_comp_eq_scalar_of_scalarCompression

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
    NoInformationOn C S → FinitePOVMDistributionInvariant.{u, v} C S := by
  intro hInformation m _ effects hPOVM i rho sigma hRho hSigma
  rcases hInformation (effects i) (hPOVM.1 i) with ⟨alpha, hAlpha⟩
  exact (trace_comp_eq_scalar_of_scalarCompression hAlpha rho hRho).trans
    (trace_comp_eq_scalar_of_scalarCompression hAlpha sigma hSigma).symm
end QEC.Semantics.QuditSubsystem
