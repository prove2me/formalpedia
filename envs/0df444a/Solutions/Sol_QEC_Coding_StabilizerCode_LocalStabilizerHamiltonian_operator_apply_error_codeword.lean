-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.operator_apply_error_codeword
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:55:24.123972+00:00
-- url     : https://prove2.me/submissions/4dd7699e-7466-4904-845e-504160823c95

import Definitions.Def_QEC_Coding_Stabilizer_ErrorPath
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_term_apply_error_codeword

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
    (E : Binary ι) (ψ : Semantics.Qubit.QubitRegister ι)
    (hψ : ψ ∈ H.code.1.code.carrier) :
    H.operator (toQubitOperator E ψ) =
      ∑ j, if j ∈ H.violatedGenerators E then
        toQubitOperator E ψ
      else
        -(toQubitOperator E ψ) := by
  rw [operator, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _hj
  exact H.term_apply_error_codeword E ψ hψ j
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
