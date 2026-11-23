-- Prove2me | solution 1 for PI.WGL.algebraMap_int_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:14.987003+00:00
-- url     : https://prove2.me/submissions/f40c5a1e-c62d-4a28-8394-c9e469f0163c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliShift
import Definitions.Def_Lemmata_GeneralBFactRight_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliZ
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


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
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL
theorem _root_.solution {N : ℕ} (lam : DomWeight N) (w : ℤ) :
    algebraMap ℂ (Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ)) (w : ℂ) ∈ presRing lam := by
  rw [map_intCast]; exact intCast_mem _ w
end PI.WGL
