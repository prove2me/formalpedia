-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.stabilizerBornWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:36:21.862386+00:00
-- url     : https://prove2.me/submissions/2a08c825-2cdb-466c-ae34-ea4c876b8b73

import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_nonneg


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
    (rho : DensityOperator (Qubit.QubitRegister ι)) :
    0 ≤ (stabilizerInstrument P).bornWeight outcome rho :=
  (stabilizerInstrument P).bornWeight_nonneg outcome rho
end QEC.Coding.PauliSymplectic
