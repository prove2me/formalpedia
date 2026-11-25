-- Prove2me | solution 1 for PI.WeylForKWork.dimension_induction_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:59:07.929708+00:00
-- url     : https://prove2.me/submissions/125c5907-47dc-4555-b6c0-b579a89390f9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStepB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStep
import Theorems.Thm_PI_WeylForKWork_dimStep_good
import Theorems.Thm_PI_WeylForKWork_dimStep_stab
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix DimensionInduction
namespace PI.WeylForKWork
theorem _root_.solution : DimStep := by
  intro p q H _ _ σ₁ σ₂ S X Y h1 h2 hcomm hS hS1 hS2 hSirr hXS hX0 hX1 hXi hYS hY0 hY2 hYi
  exact main (dimStep_good h1) (dimStep_good h2)
    (fun g g' v => by
      show σ₁ g.1 (σ₂ g'.1 v) = σ₂ g'.1 (σ₁ g.1 v)
      rw [← ContinuousLinearMap.comp_apply, hcomm _ g.2 _ g'.2]
      rfl)
    (dimStep_stab.1 hS1) (dimStep_stab.1 hS2)
    (fun S' h s1 s2 => hSirr S' h (dimStep_stab.2 s1) (dimStep_stab.2 s2))
    hXS hX0 (dimStep_stab.1 hX1) (fun X' h s => hXi X' h (dimStep_stab.2 s))
    hYS hY0 (dimStep_stab.1 hY2) (fun Y' h s => hYi Y' h (dimStep_stab.2 s))
end PI.WeylForKWork
