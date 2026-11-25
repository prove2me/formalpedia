-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.hJ_span_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:52.316481+00:00
-- url     : https://prove2.me/submissions/ff8f334d-39f2-4246-ad96-84a73cd48582

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_add_right
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_smul_right
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_zero_right

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
    (h : ∀ a ∈ S, hJ ε y a = 0) : hJ ε y x = 0 := by
  induction hx using Submodule.span_induction with
  | mem a ha => exact h a ha
  | zero => exact hJ_zero_right ε y
  | add a b _ _ ha hb => rw [hJ_add_right, ha, hb, add_zero]
  | smul c a _ ha => rw [hJ_smul_right, ha, mul_zero]
end PI.ScPiBuildW.Loc
