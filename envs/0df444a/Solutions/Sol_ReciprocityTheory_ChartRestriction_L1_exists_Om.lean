-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.exists_Om
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:00:18.127378+00:00
-- url     : https://prove2.me/submissions/d6f03e92-a063-40bd-9848-82199b0fc02a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (d : ℕ) {z : ℂ} (hz : IsIntegral ℤ z) : ∃ x : Om d, (x : ℂ) = z ∧ IsIntegral ℤ x := by
  have hzK : IsIntegral (KQ d) z := hz.tower_top
  have hmem : z ∈ Om d := hzK
  refine ⟨⟨z, hmem⟩, rfl, ?_⟩
  exact (isIntegral_algHom_iff (x := (⟨z, hmem⟩ : Om d)) (algebraMap (Om d) ℂ).toIntAlgHom
    (algebraMap (Om d) ℂ).injective).mp hz
end ReciprocityTheory.ChartRestriction.L1
