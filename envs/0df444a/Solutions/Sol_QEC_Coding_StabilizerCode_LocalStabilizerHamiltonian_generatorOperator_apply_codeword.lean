-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorOperator_apply_codeword
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:52:50.362208+00:00
-- url     : https://prove2.me/submissions/8f130ad3-f2a1-4516-92d2-7795ba42fd87

import Definitions.Def_QEC_Coding_Stabilizer_ErrorPath
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generator_mem_generatedGroup


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
open scoped Classical
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
theorem _root_.solution
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (ψ : Semantics.Qubit.QubitRegister ι)
    (hψ : ψ ∈ H.code.1.code.carrier) (j : κ) :
    H.generatorOperator j ψ = ψ := by
  exact
    (H.code.2.2 ψ).1 hψ (H.generators j)
      (H.generator_mem_generatedGroup j)
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
