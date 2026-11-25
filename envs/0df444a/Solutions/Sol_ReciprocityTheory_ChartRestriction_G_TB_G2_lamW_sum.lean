-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.lamW_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:31:24.458866+00:00
-- url     : https://prove2.me/submissions/6a088d2e-bdc1-4e60-a76d-2b9dffd280d4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SumSplitsEvalTwoWord
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateDerivationEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_lamW_add

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
theorem _root_.solution (s : Finset ι) (f : ι → MvPolynomial ι k) :
    lamW ψ (∑ i ∈ s, f i) = ∑ i ∈ s, lamW ψ (f i) := by
  let L : MvPolynomial ι k →+ k :=
    { toFun := lamW ψ, map_zero' := by simpa using lamW_add ψ 0 0, map_add' := lamW_add ψ }
  exact map_sum L f s
end ReciprocityTheory.ChartRestriction.G.TB.G2
