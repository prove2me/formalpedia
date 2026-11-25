-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.smul_of_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:47:33.207675+00:00
-- url     : https://prove2.me/submissions/eb61058c-e313-4ca1-aeb0-246b307c64f7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {k : ℤ} (g : ModularForm 𝒮ℒ k) (γ : SL(2, ℤ)) (τ : ℍ) :
    g (γ • τ) = denom γ τ ^ k * g τ := by
  have h := SlashInvariantForm.slash_action_eqn'' g (γ := Matrix.SpecialLinearGroup.mapGL ℝ γ)
    (MonoidHom.mem_range.mpr ⟨γ, rfl⟩) τ
  exact h
end ReciprocityTheory.ChartRestriction.L1
