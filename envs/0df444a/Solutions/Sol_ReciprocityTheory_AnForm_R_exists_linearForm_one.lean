-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.exists_linearForm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:08:35.509894+00:00
-- url     : https://prove2.me/submissions/2241eba2-d6ba-4944-ad31-e1c1828f24d5

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExtCContract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution : ∃ ℓ : ℂ →ₗ[ℚ] ℚ, ℓ 1 = 1 := by
  have h : ¬ ∀ φ : Module.Dual ℚ ℂ, φ 1 = 0 := by
    rw [Module.forall_dual_apply_eq_zero_iff]
    exact one_ne_zero
  push Not at h
  obtain ⟨φ, hφ⟩ := h
  exact ⟨(φ 1)⁻¹ • φ, by simp [hφ]⟩
end ReciprocityTheory.AnForm.R
