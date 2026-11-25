-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.orth_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:25.031816+00:00
-- url     : https://prove2.me/submissions/cb144c64-663a-49fe-9ead-2afbb519b7bf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_nondeg_right
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_span_left
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_fam_span

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
open PI.ScPiBuildW.Loc.LocFrame
variable {n r k : ℕ} {ε : Fin n → Bool} (L : LocFrame n r k ε)
namespace PI.ScPiBuildW.Loc.LocFrame
theorem _root_.solution (y : Fin n → ℂ) (he : ∀ a, hJ ε (L.e a) y = 0) (hf : ∀ a, hJ ε (L.f a) y = 0)
    (hz : hJ ε L.z y = 0) (hw : ∀ c, hJ ε (L.w c) y = 0) : y = 0 := by
  apply hJ_nondeg_right ε y
  intro x
  have hx : x ∈ Submodule.span ℂ (Set.range L.fam) := by
    rw [L.fam_span]
    trivial
  apply hJ_span_left ε hx
  rintro _ ⟨((a | a) | (⟨⟩ | c)), rfl⟩
  · exact he a
  · exact hf a
  · exact hz
  · exact hw c
end PI.ScPiBuildW.Loc.LocFrame
