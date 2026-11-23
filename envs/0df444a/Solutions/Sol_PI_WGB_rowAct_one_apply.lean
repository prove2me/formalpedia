-- Prove2me | solution 1 for PI.WGB.rowAct_one_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:20.728244+00:00
-- url     : https://prove2.me/submissions/c21d59b3-1e8a-468d-a3c7-b6c475e367b1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
import Theorems.Thm_Formalism_UG_P_wlocal_rowAct_one


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
theorem _root_.solution {R : Type} [CommRing R] {r c : ℕ} (p : MvPolynomial (Fin r × Fin c) R) :
    rowAct R (1 : Matrix (Fin r) (Fin r) R) p = p := by
  rw [Formalism.UG.P.wlocal_rowAct_one]; rfl
end PI.WGB
