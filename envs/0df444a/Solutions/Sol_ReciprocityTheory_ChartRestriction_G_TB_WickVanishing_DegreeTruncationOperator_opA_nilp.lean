-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator.opA_nilp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:12:16.082019+00:00
-- url     : https://prove2.me/submissions/5643f932-86df-4d74-8131-13b6385fe28a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_opA_pow_eq_zero

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
open MvPolynomial Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
open SecondColumnDegree
variable {k : Type} [CommRing k] [Algebra ℚ k]
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
theorem _root_.solution (c : σ → σ → k) (t : k) (N : ℕ) : IsNilpotent (opA c t N) := ⟨N + 1, opA_pow_eq_zero c t N⟩
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
