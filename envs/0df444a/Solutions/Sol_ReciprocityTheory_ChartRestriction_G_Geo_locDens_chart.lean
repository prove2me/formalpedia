-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.locDens_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:26:20.695207+00:00
-- url     : https://prove2.me/submissions/d358d4ac-d1de-4a76-933a-e70c74cc8aa5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeI
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeJ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeO
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeQ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeA
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDensChart


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
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (j k : Fin A.n) (y : Fin e → ℂ)
    (hy : y ∈ (A.chart j).target) (hk : (A.chart j).symm y ∈ (A.chart k).source) :
    locDens A Φ j y = locDens A Φ k (A.chart k ((A.chart j).symm y)) *
      ‖LinearMap.det (fderiv ℂ (A.chart k ∘ (A.chart j).symm) y :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2 :=
  locDensChart A Φ hΦ j k y hy hk
end ReciprocityTheory.ChartRestriction.G.Geo
