-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.hJ_span_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:20:04.459057+00:00
-- url     : https://prove2.me/submissions/5b5ea4a7-d118-47f4-9e68-d9e7a5362813

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_add_left
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_smul_left
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_zero_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PI PI.ScPiBuildW PI.ScPiBuildW.Loc
open PI.ScPiExists
variable {n : ℕ} (ε : Fin n → Bool)
namespace PI.ScPiBuildW.Loc
theorem _root_.solution {S : Set (Fin n → ℂ)} {x y : Fin n → ℂ} (hx : x ∈ Submodule.span ℂ S)
    (h : ∀ a ∈ S, hJ ε a y = 0) : hJ ε x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem a ha => exact h a ha
  | zero => exact hJ_zero_left ε y
  | add a b _ _ ha hb => rw [hJ_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [hJ_smul_left, ha, mul_zero]
end PI.ScPiBuildW.Loc
