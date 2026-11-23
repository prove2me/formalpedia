-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.lamW_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:09.537772+00:00
-- url     : https://prove2.me/submissions/b48d936a-cf2b-4991-bc99-b224db407bf8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SumSplitsEvalTwoWord
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateDerivationEq

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {d : ℕ}
variable {ι : Type} [Fintype ι] [DecidableEq ι] (ψ : List ι → k)
namespace ReciprocityTheory.ChartRestriction.G.TB.G2
theorem _root_.solution (P Q : MvPolynomial ι k) : lamW ψ (P + Q) = lamW ψ P + lamW ψ Q := by
  show (AddMonoidAlgebra.coeff P + AddMonoidAlgebra.coeff Q).sum _ = _
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)
end ReciprocityTheory.ChartRestriction.G.TB.G2
