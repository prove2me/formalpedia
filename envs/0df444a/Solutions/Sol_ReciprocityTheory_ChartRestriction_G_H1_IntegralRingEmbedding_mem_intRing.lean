-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding.mem_intRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:53:01.515848+00:00
-- url     : https://prove2.me/submissions/fd87299b-6454-4d6b-8a2d-93dbf21d3acd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_NakayamaChar
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IntegralRingEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
open Module
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))
namespace ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
theorem _root_.solution {a : F} : a ∈ intRing v ↔ 0 ≤ v a := Iff.rfl
end ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
