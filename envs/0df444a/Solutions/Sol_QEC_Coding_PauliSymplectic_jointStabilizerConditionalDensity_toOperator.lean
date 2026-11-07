-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:55:49.355035+00:00
-- url     : https://prove2.me/submissions/5b5ec0dc-ede9-46b3-ad1f-457602aa82f0

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_branchOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator



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
    (hpos : 0 < (jointStabilizerInstrument checks hcomm).bornWeight syndrome rho) :
    (jointStabilizerConditionalDensity checks hcomm syndrome rho hpos).toOperator =
      (((jointStabilizerInstrument checks hcomm).bornWeight syndrome rho : Complex)⁻¹) •
        (jointStabilizerProjector checks hcomm syndrome * rho.toOperator *
          jointStabilizerProjector checks hcomm syndrome) := by
  rw [jointStabilizerConditionalDensity,
    FiniteInstrument.conditionalDensity_toOperator,
    jointStabilizerInstrument_branchOperator]
end QEC.Coding.PauliSymplectic
