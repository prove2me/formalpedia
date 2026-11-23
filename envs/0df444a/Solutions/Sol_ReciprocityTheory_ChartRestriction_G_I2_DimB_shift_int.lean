-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimB.shift_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:01.346097+00:00
-- url     : https://prove2.me/submissions/7caa89e3-e4a3-4fa1-82a9-3d6a200a935e

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
theorem _root_.solution {G β : Type*} [AddCommGroup G] (Φ : G → β) (e : G) (h : ∀ v, Φ (v + e) = Φ v)
    (c : ℤ) (v : G) : Φ (v + c • e) = Φ v := by
  induction c using Int.induction_on generalizing v with
  | zero => simp
  | succ n ih => rw [add_smul, one_smul, ← add_assoc, h, ih]
  | pred n ih =>
    rw [← ih v, ← h (v + (-(n : ℤ) - 1) • e)]
    congr 1
    rw [sub_smul, one_smul, neg_smul]; abel
end ReciprocityTheory.ChartRestriction.G.I2.DimB
