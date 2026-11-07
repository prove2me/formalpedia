-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.stabilizerBranchOperator_eq_zero_of_bornWeight_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:36:35.782442+00:00
-- url     : https://prove2.me/submissions/894e2ec6-d0ad-4dda-a836-434274b4fa1b

import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_eq_zero_of_bornWeight_eq_zero


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open Semantics
open scoped BigOperators
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    (P : Binary ι) (outcome : StabilizerOutcome)
    (rho : DensityOperator (Qubit.QubitRegister ι))
    (hzero : (stabilizerInstrument P).bornWeight outcome rho = 0) :
    (stabilizerInstrument P).branchOperator outcome rho.toOperator = 0 :=
  (stabilizerInstrument P).branchOperator_eq_zero_of_bornWeight_eq_zero
    outcome rho hzero
end QEC.Coding.PauliSymplectic
