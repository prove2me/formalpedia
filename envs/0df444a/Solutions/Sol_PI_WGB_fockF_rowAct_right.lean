-- Prove2me | solution 1 for PI.WGB.fockF_rowAct_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:05:36.556419+00:00
-- url     : https://prove2.me/submissions/0aa58ed1-98b4-4767-9e96-b753211c6840

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockRowAdj


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
open Formalism.REAL (fockF)
namespace PI.WGB
theorem _root_.solution (r n : ℕ) (M : Matrix (Fin r) (Fin r) ℂ) (p q : MvPolynomial (Fin r × Fin n) ℂ) :
    fockF p (rowAct ℂ M q) = fockF (rowAct ℂ M.conjTranspose p) q := by
  rw [fockRowAdj r n M.conjTranspose p q, Matrix.conjTranspose_conjTranspose]
end PI.WGB
