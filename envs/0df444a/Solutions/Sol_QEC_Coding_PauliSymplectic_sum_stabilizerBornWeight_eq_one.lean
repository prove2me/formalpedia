-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.sum_stabilizerBornWeight_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:36:32.81395+00:00
-- url     : https://prove2.me/submissions/92998264-aab2-4648-8571-76923768ff95

import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_bornWeight_eq_one


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
    (P : Binary ι)
    (rho : DensityOperator (Qubit.QubitRegister ι)) :
    ∑ outcome : StabilizerOutcome,
        (stabilizerInstrument P).bornWeight outcome rho = 1 :=
  (stabilizerInstrument P).sum_bornWeight_eq_one
    (stabilizerKrausFamily_complete P) rho
end QEC.Coding.PauliSymplectic
