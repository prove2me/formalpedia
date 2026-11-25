-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator.cS_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:59:02.39292+00:00
-- url     : https://prove2.me/submissions/763f91d3-4dc4-46e6-9db4-d0d2b19dd775

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator

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
variable {ι : Type} [Fintype ι] {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
theorem _root_.solution (c : ι → ι → k) :
    cS c (univ : Finset (Fin n)) = fun p q => if p.2 = q.2 then c p.1 q.1 else 0 := by
  unfold cS cB
  funext p q
  by_cases h : p.2 = q.2
  · rw [if_pos h]
    simp only [← h, and_self, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b _ => if_neg ?_
    rintro ⟨h1, h2⟩
    exact h (h1.trans h2.symm)
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
