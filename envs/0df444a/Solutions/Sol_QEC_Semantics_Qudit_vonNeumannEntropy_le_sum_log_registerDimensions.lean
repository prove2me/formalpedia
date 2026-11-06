-- Prove2me | solution 1 for QEC.Semantics.Qudit.vonNeumannEntropy_le_sum_log_registerDimensions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:33:18.295388+00:00
-- url     : https://prove2.me/submissions/f44a3369-79f2-48cd-9732-16beba9203f6

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_le_log_finrank
import Theorems.Thm_QEC_Semantics_Qudit_dimensions_positive_of_density
import Theorems.Thm_QEC_Semantics_Qudit_log_finrank_quditRegister_eq_sum_log_dimensions

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.Qudit
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.Qudit
theorem _root_.solution (q : ι -> Nat)
    (rho : DensityOperator (QuditRegister q)) :
    rho.vonNeumannEntropy <= ∑ i, Real.logb 2 (q i : Real) := by
  calc
    rho.vonNeumannEntropy <= Real.logb 2 (Module.finrank Complex (QuditRegister q) : Real) :=
      rho.vonNeumannEntropy_le_log_finrank
    _ = ∑ i, Real.logb 2 (q i : Real) :=
      log_finrank_quditRegister_eq_sum_log_dimensions q
        (dimensions_positive_of_density q rho)
end QEC.Semantics.Qudit
