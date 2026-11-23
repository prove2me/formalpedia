-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.KrullColonIdeal.mem_colonI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:32.046436+00:00
-- url     : https://prove2.me/submissions/604f098a-7526-44f4-b599-bbfbb50f5a00

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegKrull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.KrullColonIdeal
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.T0.KrullColonIdeal
theorem _root_.solution {s c r : R} : r ∈ colonI s c ↔ r * c ∈ Ideal.span {s} := Iff.rfl
end ReciprocityTheory.ChartRestriction.G.T0.KrullColonIdeal
