-- Prove2me | solution 1 for PI.WGB.elemGL_apply_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:16:39.947288+00:00
-- url     : https://prove2.me/submissions/1c9d9468-ad6b-4039-941e-a7f86f12f023

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFactsProofA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetEmbUnitriA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_CoeffRowActDiagA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
variable {n : ℕ}
namespace PI.WGB
theorem _root_.solution (a b : Fin n) (hab : a ≠ b) (t : ℂ) (i j : Fin n) :
    ((elemGL_A a b hab t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j =
      (if i = j then 1 else 0) + (if a = i ∧ b = j then t else 0) := by
  show (1 + Matrix.single a b t) i j = _
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
end PI.WGB
