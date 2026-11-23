-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Hf_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:23:14.726651+00:00
-- url     : https://prove2.me/submissions/8e898218-34a2-4fca-a727-4bbcd4928650

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
section basic
variable {ι : Type} [Fintype ι]
private theorem Hf_eq_inner_swap_complex (v w : EuclideanSpace ℂ ι) : Hf v w = inner ℂ w v := by
  simp [Hf, PiLp.inner_apply, RCLike.inner_apply]
end basic
variable {E : Type} [Field E] [NumberField E]
section vecU
variable {dim : (E →+* ℂ) → ℕ}
end vecU
end
end ReciprocityTheory.ChartRestriction.G.I2
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (v w : EuclideanSpace ℂ ι) : Hf w v = (starRingEnd ℂ) (Hf v w) := by
  rw [Hf_eq_inner_swap_complex, Hf_eq_inner_swap_complex]
  exact (inner_conj_symm _ _).symm
end ReciprocityTheory.ChartRestriction.G.I2
