-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.jointStabilizerBranchOperator_eq_zero_of_bornWeight_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:37:14.228929+00:00
-- url     : https://prove2.me/submissions/844e236a-8e1f-41c1-af8f-6c07b45f31b8

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_eq_zero_of_bornWeight_eq_zero


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open Semantics
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (rho : DensityOperator (Qubit.QubitRegister ι))
    (hzero : (jointStabilizerInstrument checks hcomm).bornWeight syndrome rho = 0) :
    (jointStabilizerInstrument checks hcomm).branchOperator syndrome rho.toOperator = 0 :=
  (jointStabilizerInstrument checks hcomm).branchOperator_eq_zero_of_bornWeight_eq_zero
    syndrome rho hzero
end QEC.Coding.PauliSymplectic
