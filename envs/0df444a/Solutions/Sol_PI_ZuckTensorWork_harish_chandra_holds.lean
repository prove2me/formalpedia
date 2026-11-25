-- Prove2me | solution 1 for PI.ZuckTensorWork.harish_chandra_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:18:38.210845+00:00
-- url     : https://prove2.me/submissions/abc0fc87-9277-48ad-9f8c-35b07987200d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_RevNum
import Theorems.Thm_PI_ZuckTensorWork_Cj_mk_un
import Theorems.Thm_PI_ZuckTensorWork_Cj_un_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.ZuckTensorWork.Cj.mk_un
attribute [local simp] PI.ZuckTensorWork.Cj.un_mk



set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
variable {n : ℕ}
namespace PI.ZuckTensorWork
theorem _root_.solution : HCRev := by
  intro n lam ⟨hs, hz⟩
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · show -lam (Fin.rev b) < -lam (Fin.rev a)
    exact neg_lt_neg (hs (Fin.rev_lt_rev.mpr hab))
  · obtain ⟨m, hm⟩ := hz (Fin.rev a)
    refine ⟨-m - (n : ℤ) + 1, ?_⟩
    simp only [revP]
    push_cast
    linarith
end PI.ZuckTensorWork
