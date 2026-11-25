-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.sum_filter_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:31:11.852048+00:00
-- url     : https://prove2.me/submissions/0286c9a0-a8ed-4cf0-a82c-215f083bb6aa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockDegOfScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K : Type} [Field K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (b : Fin (D + 1)) (s : TVar D N →₀ ℕ) :
    (∑ v ∈ Finset.univ.filter (fun v : TVar D N => v.1 = b), s v) = ∑ j, s (b, j) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine (Finset.sum_eq_single b (fun c _ hc => Finset.sum_eq_zero fun j _ => if_neg hc)
    (by simp)).trans (Finset.sum_congr rfl fun j _ => if_pos rfl)
end ReciprocityTheory.ChartRestriction.G.T0
