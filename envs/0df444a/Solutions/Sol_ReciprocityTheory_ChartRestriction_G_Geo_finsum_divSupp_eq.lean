-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.finsum_divSupp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:31.938512+00:00
-- url     : https://prove2.me/submissions/5fe1a9e0-d00b-474a-a7f2-26937bc91269

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (s : MRing ι) (g : Ideal (MRing ι) → ℝ) :
    (∑ᶠ (W') (_ : W' ∈ divSupp P s ∧ IsHorizontal W'), g W') =
      ∑ W' ∈ ((divSupp_finite P s).subset (fun _ h => h.1) :
        {W' | W' ∈ divSupp P s ∧ IsHorizontal W'}.Finite).toFinset, g W' :=
  finsum_mem_eq_finite_toFinset_sum g _
end ReciprocityTheory.ChartRestriction.G.Geo
