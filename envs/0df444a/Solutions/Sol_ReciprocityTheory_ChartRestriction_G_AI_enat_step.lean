-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.enat_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:27:43.9528+00:00
-- url     : https://prove2.me/submissions/7f7c73d2-fd93-4fa7-87bc-aeb7505c3891

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module PrimeSpectrum
open scoped Pointwise
universe u v
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {k1 k3 c2 k2 c1 c3 s1 s3 : ℕ∞} (h1 : k1 ≠ ⊤) (h3 : k3 ≠ ⊤) (hc1 : c1 ≠ ⊤)
    (hc3 : c3 ≠ ⊤) (hc2 : c2 ≠ ⊤) (e1 : c1 = k1 + s1) (e3 : c3 = k3 + s3)
    (eu : k1 + k3 + c2 = k2 + c1 + c3) : k2 ≠ ⊤ ∧ c2 = k2 + (s1 + s3) := by
  have hs1 : s1 ≠ ⊤ := by
    rintro rfl
    rw [add_top] at e1
    exact hc1 e1
  have hs3 : s3 ≠ ⊤ := by
    rintro rfl
    rw [add_top] at e3
    exact hc3 e3
  have hk2 : k2 ≠ ⊤ := by
    rintro rfl
    rw [top_add, top_add] at eu
    lift k1 to ℕ using h1
    lift k3 to ℕ using h3
    lift c2 to ℕ using hc2
    exact absurd eu (by simp)
  refine ⟨hk2, ?_⟩
  lift k1 to ℕ using h1
  lift k3 to ℕ using h3
  lift s1 to ℕ using hs1
  lift s3 to ℕ using hs3
  lift k2 to ℕ using hk2
  lift c2 to ℕ using hc2
  subst e1 e3
  norm_cast at eu ⊢
  omega
end ReciprocityTheory.ChartRestriction.G.AI
