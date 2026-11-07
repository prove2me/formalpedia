-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.sum_jointStabilizerBornWeight_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:37:04.139277+00:00
-- url     : https://prove2.me/submissions/25063849-451b-455f-920d-c2cbd6b37080

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_bornWeight_eq_one


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
    (rho : DensityOperator (Qubit.QubitRegister ι)) :
    ∑ syndrome : JointSyndrome κ,
        (jointStabilizerInstrument checks hcomm).bornWeight syndrome rho = 1 :=
  (jointStabilizerInstrument checks hcomm).sum_bornWeight_eq_one
    (jointStabilizerKrausFamily_complete checks hcomm) rho
end QEC.Coding.PauliSymplectic
