-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.jointStabilizerBornWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:36:45.567462+00:00
-- url     : https://prove2.me/submissions/b4da9848-8dae-45ba-af23-8720beb36c14

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_nonneg


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
    (syndrome : JointSyndrome κ) (rho : DensityOperator (Qubit.QubitRegister ι)) :
    0 ≤ (jointStabilizerInstrument checks hcomm).bornWeight syndrome rho :=
  (jointStabilizerInstrument checks hcomm).bornWeight_nonneg syndrome rho
end QEC.Coding.PauliSymplectic
