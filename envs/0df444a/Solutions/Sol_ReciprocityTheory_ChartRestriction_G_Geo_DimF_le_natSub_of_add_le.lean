-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.DimF.le_natSub_of_add_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:33.325235+00:00
-- url     : https://prove2.me/submissions/b10cc7bd-2564-4e53-ac82-eeaab7577f85

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.DimF
variable {A : Type*} [CommRing A]
namespace ReciprocityTheory.ChartRestriction.G.Geo.DimF
theorem _root_.solution {k n : ℕ} {x : ℕ∞} (h : (k : ℕ∞) + x ≤ n) : x ≤ ((n - k : ℕ) : ℕ∞) := by
  induction x using ENat.recTopCoe with
  | top => simp at h
  | coe m =>
    have h1 : k + m ≤ n := by exact_mod_cast h
    exact_mod_cast (by omega : m ≤ n - k)
end ReciprocityTheory.ChartRestriction.G.Geo.DimF
