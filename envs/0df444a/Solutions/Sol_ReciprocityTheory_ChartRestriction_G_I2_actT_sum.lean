-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.actT_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:10:41.038576+00:00
-- url     : https://prove2.me/submissions/88dad396-07e7-4014-854f-ac16824d5ded

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]
variable {dim : (E →+* ℂ) → ℕ}
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {ι : Type} (s : Finset ι) (c : ι → ℝ) (t : ι → (E →+* ℂ) → ℂ) (v : Vsp dim) :
    actT (∑ k ∈ s, c k • t k) v = ∑ k ∈ s, c k • actT (t k) v := by
  ext i
  simp [actT, Finset.sum_mul, Complex.real_smul, mul_assoc]
end ReciprocityTheory.ChartRestriction.G.I2
