-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimB.shift_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:56.03358+00:00
-- url     : https://prove2.me/submissions/f42e0a51-3072-47f9-9ff7-5a5c87320d0c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Complex
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.DimB
variable {k : ℕ}
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_11
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_13
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_16
namespace ReciprocityTheory.ChartRestriction.G.I2.DimB
theorem _root_.solution {G β ι : Type*} [AddCommMonoid G] (Φ : G → β) (a : ι → G)
    (h : ∀ l v, Φ (v + a l) = Φ v) (S : Finset ι) (v : G) : Φ (v + ∑ l ∈ S, a l) = Φ v := by
  classical
  induction S using Finset.induction_on generalizing v with
  | empty => simp
  | insert b S hb ih => rw [Finset.sum_insert hb, ← add_assoc, ih, h]
end ReciprocityTheory.ChartRestriction.G.I2.DimB
