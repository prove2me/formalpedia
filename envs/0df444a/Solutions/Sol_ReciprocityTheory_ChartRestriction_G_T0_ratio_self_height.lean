-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ratio_self_height
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:34:25.50161+00:00
-- url     : https://prove2.me/submissions/695be006-fb85-44a0-8d72-e333b40e36d6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ratio_eq_of_eq_smul

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
theorem _root_.solution {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {f : V}
    (hf : f ≠ 0) : ratio (Ω := Ω) f f = 1 := ratio_eq_of_eq_smul hf (one_smul Ω f).symm
end ReciprocityTheory.ChartRestriction.G.T0
