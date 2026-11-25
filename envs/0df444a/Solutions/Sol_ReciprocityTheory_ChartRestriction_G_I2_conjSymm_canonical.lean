-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.conjSymm_canonical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:10:12.392723+00:00
-- url     : https://prove2.me/submissions/32f6f2fd-a03e-4baa-94c8-195cf70edce4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (x : E) : ConjSymm (canonicalEmbedding E x) := fun σ => by
  simp only [canonicalEmbedding.apply_at, ComplexEmbedding.conjugate_coe_eq]
end ReciprocityTheory.ChartRestriction.G.I2
