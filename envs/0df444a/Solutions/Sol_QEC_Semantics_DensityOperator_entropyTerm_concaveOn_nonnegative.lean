-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.entropyTerm_concaveOn_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:16:13.167692+00:00
-- url     : https://prove2.me/submissions/c83eb7f6-0856-4d05-8c7b-5d0a07e4a528

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Theorems.Thm_QEC_Semantics_DensityOperator_entropyTerm_eq_negMulLog_div_logTwo

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution :
    ConcaveOn Real (Set.Ici (0 : Real)) entropyTerm := by
  rw [show entropyTerm = fun x => (Real.log 2)⁻¹ • Real.negMulLog x from
    funext entropyTerm_eq_negMulLog_div_logTwo]
  exact Real.concaveOn_negMulLog.smul (by positivity)
end QEC.Semantics.DensityOperator
