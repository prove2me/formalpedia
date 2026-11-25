-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.gtB_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:30:25.443222+00:00
-- url     : https://prove2.me/submissions/916fe39b-79cb-4494-880e-a109415826e4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MeasureTheory Module Submodule
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (n : ℕ) : (innerₗ (EuclideanSpace ℝ (Fin n))).Nondegenerate := by
  show _ ∧ _
  constructor
  · intro x hx
    first
      | simpa using hx x
      | simpa [innerₗ_apply_apply] using hx x
  · intro y hy
    first
      | simpa using hy y
      | simpa [innerₗ_apply_apply] using hy y
end ReciprocityTheory.ChartRestriction.G.T0
