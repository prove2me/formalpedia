-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:46:19.320784+00:00
-- url     : https://prove2.me/submissions/7049ed35-7ac2-4526-9d9f-ae56c2c66063

import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_branchOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator



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
    (hpos : 0 < (stabilizerInstrument P).bornWeight outcome rho) :
    (stabilizerConditionalDensity P outcome rho hpos).toOperator =
      (((stabilizerInstrument P).bornWeight outcome rho : Complex)⁻¹) •
        (stabilizerProjector P outcome * rho.toOperator *
          stabilizerProjector P outcome) := by
  rw [stabilizerConditionalDensity,
    FiniteInstrument.conditionalDensity_toOperator,
    stabilizerInstrument_branchOperator]
end QEC.Coding.PauliSymplectic
