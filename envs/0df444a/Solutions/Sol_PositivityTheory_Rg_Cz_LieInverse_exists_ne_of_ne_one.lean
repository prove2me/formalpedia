-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.LieInverse.exists_ne_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:55.001805+00:00
-- url     : https://prove2.me/submissions/e83c7ff6-829b-4714-ac95-904322d6c0f0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PLieInv
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.LieInverse
namespace PositivityTheory.Rg.Cz.LieInverse
theorem _root_.solution {n : ℕ} (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) (i : Fin n) :
    ∃ j, j ≠ i ∧ σ j ≠ j := by
  by_contra h
  push Not at h
  apply hσ
  have hi : σ i = i := by
    by_contra hne
    have := h (σ i) hne
    exact hne (σ.injective this)
  ext j
  by_cases hj : j = i
  · subst hj; simp [hi]
  · simp [h j hj]
end PositivityTheory.Rg.Cz.LieInverse
