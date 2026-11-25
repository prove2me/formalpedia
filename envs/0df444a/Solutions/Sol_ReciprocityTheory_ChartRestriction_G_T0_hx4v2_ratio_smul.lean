-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hx4v2_ratio_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:16.405804+00:00
-- url     : https://prove2.me/submissions/cab3767c-7448-4979-82f5-40056b0fb908

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BasisBlock0
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormGenericRatioSpec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {g : V}
    (hg : g ≠ 0) (s : Ω) : ratio (Ω := Ω) (s • g) g = s := by
  unfold ratio
  have hex : ∃ a : Ω, s • g = a • g := ⟨s, rfl⟩
  rw [dif_pos hex]
  exact (smul_left_injective Ω hg hex.choose_spec).symm
end ReciprocityTheory.ChartRestriction.G.T0
