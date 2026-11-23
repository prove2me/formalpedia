-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.IsU.unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:08.616241+00:00
-- url     : https://prove2.me/submissions/6805f657-dee7-43dc-b7fe-10c1af11c2b2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
variable {dim : (E →+* ℂ) → ℕ}
namespace ReciprocityTheory.ChartRestriction.G.I2
namespace IsU
theorem _root_.solution {I : Submodule ℤ (Vsp dim)} {x u u' : Vsp dim} (h : IsU I x u)
    (h' : IsU I x u') : u = u' := by
  have hd : u - u' ∈ IR I := Submodule.sub_mem _ h.1 h'.1
  have h0 : inner ℝ (u - u') (u - u') = (0 : ℝ) := by
    rw [inner_sub_left, h.2 _ hd, h'.2 _ hd, sub_self]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)
end IsU
end ReciprocityTheory.ChartRestriction.G.I2
