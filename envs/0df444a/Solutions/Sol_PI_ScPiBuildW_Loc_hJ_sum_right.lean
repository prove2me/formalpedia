-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.hJ_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:19:53.968284+00:00
-- url     : https://prove2.me/submissions/8eec6d97-8b89-46d5-addd-ebfafadd2899

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_add_right
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_smul_right
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_zero_right
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PI PI.ScPiBuildW PI.ScPiBuildW.Loc
open PI.ScPiExists
variable {n : ℕ} (ε : Fin n → Bool)
namespace PI.ScPiBuildW.Loc
theorem _root_.solution {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (c : ι → ℂ) (u : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, c i • u i) = ∑ i ∈ s, c i * hJ ε x (u i) := by
  classical
  refine Finset.induction_on s (by simp [hJ_zero_right]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, hJ_add_right, hJ_smul_right, ih]
end PI.ScPiBuildW.Loc
