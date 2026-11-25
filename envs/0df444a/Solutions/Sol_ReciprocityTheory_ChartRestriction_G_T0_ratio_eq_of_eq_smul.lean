-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ratio_eq_of_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:09:53.817025+00:00
-- url     : https://prove2.me/submissions/50586362-c00d-441d-a9e0-f41b6853428c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight

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
theorem _root_.solution {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {f g : V} {a : Ω}
    (hg : g ≠ 0) (h : f = a • g) : ratio f g = a := by
  unfold ratio
  have hex : ∃ a' : Ω, f = a' • g := ⟨a, h⟩
  rw [dif_pos hex]
  have hs : a • g = hex.choose • g := by
    rw [← h]
    exact hex.choose_spec
  exact (smul_left_injective Ω hg hs).symm
end ReciprocityTheory.ChartRestriction.G.T0
