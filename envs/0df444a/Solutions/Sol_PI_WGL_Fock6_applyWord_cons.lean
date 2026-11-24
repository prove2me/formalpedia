-- Prove2me | solution 1 for PI.WGL.Fock6.applyWord_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:37.378808+00:00
-- url     : https://prove2.me/submissions/f0551b12-d84d-4c36-b121-c704c0c1fbaa

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftFock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.REAL MvPolynomial
open PI.WGL.Fock6
namespace PI.WGL.Fock6
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} (x : Fin r × Fin r × ℕ) (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) :
    applyWord R (x :: w) f = rowDiv R x.1 x.2.1 x.2.2 (applyWord R w f) := rfl
end PI.WGL.Fock6
