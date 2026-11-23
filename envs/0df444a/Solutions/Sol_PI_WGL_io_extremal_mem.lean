-- Prove2me | solution 1 for PI.WGL.io_extremal_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:29.948334+00:00
-- url     : https://prove2.me/submissions/38fd25f6-cabf-49c8-9be4-a4503da41c2c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_PeriodIntegrals_GTBranch
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoExistsOfCap

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
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL
theorem _root_.solution (h3 : PI.HwIrred) (k : ℕ) (mu : DomWeight k) :
    extremal ℂ k mu ∈ nablaSq ℂ k mu := by
  rw [(h3 k mu).1]
  exact Submodule.subset_span ⟨[], rfl⟩
end PI.WGL
