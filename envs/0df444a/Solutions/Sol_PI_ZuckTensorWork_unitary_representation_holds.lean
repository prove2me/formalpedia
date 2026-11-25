-- Prove2me | solution 1 for PI.ZuckTensorWork.unitary_representation_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:35:11.646962+00:00
-- url     : https://prove2.me/submissions/73090302-780c-4c4b-8b2c-fcbc7e1c543e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ConjRep
import Theorems.Thm_PI_ZuckTensorWork_revM_mul
import Theorems.Thm_PI_ZuckTensorWork_revM_one
import Theorems.Thm_PI_ZuckTensorWork_continuous_revM
import Theorems.Thm_PI_ZuckTensorWork_revM_mem_UJset
import Theorems.Thm_PI_ZuckTensorWork_Cj_continuous_mk
import Theorems.Thm_PI_ZuckTensorWork_cjOp_one
import Theorems.Thm_PI_ZuckTensorWork_cjOp_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open PI PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
namespace PI.ZuckTensorWork
theorem _root_.solution : URepConj := by
  intro n ε H _ _ σ ⟨⟨h1, hmul⟩, hiso, hcont⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show cjOp (σ (revM 1)) = 1
    rw [revM_one, h1, cjOp_one]
  · intro a ha b hb
    show cjOp (σ (revM (a * b))) = (cjOp (σ (revM a))).comp (cjOp (σ (revM b)))
    rw [revM_mul, hmul _ (revM_mem_UJset ha) _ (revM_mem_UJset hb), cjOp_comp]
  · intro g hg v
    exact hiso _ (revM_mem_UJset hg) (Cj.un v)
  · intro v
    have hc : ContinuousOn (fun g => σ (revM g) (Cj.un v)) (UJset (revE ε)) :=
      (hcont (Cj.un v)).comp continuous_revM.continuousOn (fun g hg => revM_mem_UJset hg)
    exact Cj.continuous_mk.comp_continuousOn hc
end PI.ZuckTensorWork
