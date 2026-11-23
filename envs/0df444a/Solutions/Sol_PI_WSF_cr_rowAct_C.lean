-- Prove2me | solution 1 for PI.WSF.cr_rowAct_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:57.158325+00:00
-- url     : https://prove2.me/submissions/609e5da7-3f45-425b-aff1-2b878d5facdd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CrRowActRowAct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WSF
open Formalism.BasicNotions MvPolynomial
namespace PI.WSF
theorem _root_.solution {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (a : ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g (C a : MvPolynomial (Fin N × Fin N) ℂ) = C a :=
  (Formalism.GradedWeylDivisibility.rowAct ℂ g).commutes a
end PI.WSF
