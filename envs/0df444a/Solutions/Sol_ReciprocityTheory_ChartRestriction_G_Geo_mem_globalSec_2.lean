-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.G.Geo.mem_globalSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:26:35.756175+00:00
-- url     : https://prove2.me/submissions/88a854b1-4202-47c2-a145-b4f533e26c38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
variable (o : Type*) {Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {ι : Type*}
variable {o}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {x : ι → Ω} {r : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
    (B : ChartBundle o x r E) (e : E) :
    e ∈ globalSec B ↔ ∀ i, x i ≠ 0 → e ∈ B.lat i := by
  simp [globalSec, AddSubgroup.mem_iInf]
end ReciprocityTheory.ChartRestriction.G.Geo
