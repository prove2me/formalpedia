-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.zero_mem_Hset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:31:12.400403+00:00
-- url     : https://prove2.me/submissions/93d1500a-9a31-4acf-af4a-22e11b1f56ae

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB
theorem _root_.solution (h : PS ℚ 2 0) : (0 : (Fin 0 → ℚ) × (Fin 0 → ℚ)) ∈ Hset (R := ℤ) ℚ h := by
  simp only [Hset, Set.mem_setOf_eq]
  exact ⟨0, 0, Prod.ext (funext fun i => i.elim0) (funext fun i => i.elim0)⟩
end ReciprocityTheory.ChartRestriction.G.TB
