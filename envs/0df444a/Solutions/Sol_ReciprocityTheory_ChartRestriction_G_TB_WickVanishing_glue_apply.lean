-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.glue_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:06:02.274624+00:00
-- url     : https://prove2.me/submissions/63cefa9e-d099-4757-8ae6-5b996a68f719

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TruncatedExpSecondEqFull

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
open MvPolynomial Finset ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open SecondColumnDegree DegreeTruncationOperator
variable {k : Type} [CommRing k] {ι : Type} [Fintype ι] {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution (g : Fin n → (ι →₀ ℕ)) (l : ι) (b : Fin n) : glue g (l, b) = g b l := by
  classical
  unfold glue
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single b]
  · exact Finsupp.mapDomain_apply (fun x y h => congrArg Prod.fst h) _ _
  · intro b' _ hb
    apply Finsupp.mapDomain_notin_range
    rintro ⟨x, hx⟩
    exact hb (congrArg Prod.snd hx)
  · intro h
    exact absurd (Finset.mem_univ b) h
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
