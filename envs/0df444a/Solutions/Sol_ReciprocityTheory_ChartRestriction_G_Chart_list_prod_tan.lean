-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.list_prod_tan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:04:07.89788+00:00
-- url     : https://prove2.me/submissions/8d7941ac-9679-4fc8-bde9-016c544b777c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftCompJetSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_one


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR epsScaleR IsTangent IsLieComb IsLieBasis)
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution : ∀ {k : ℕ} (u : Fin k → (sp (R₀ := R) (DualNumber R) ⟶ G))
    (hu : ∀ i, IsTan (u i)), ∃ h : IsTan (List.ofFn u).prod, tcoord hx _ h = ∑ i, tcoord hx (u i) (hu i)
  | 0, u, hu => by
    have e0 : (List.ofFn u).prod = 1 := by simp
    refine ⟨e0 ▸ isTan_one, ?_⟩
    rw [tcoord_congr hx e0 _ isTan_one, tcoord_one]
    simp
  | k + 1, u, hu => by
    obtain ⟨h, e⟩ := solution (fun i => u i.succ) (fun i => hu i.succ)
    have e0 : (List.ofFn u).prod = u 0 * (List.ofFn fun i => u i.succ).prod := by
      rw [List.ofFn_succ, List.prod_cons]
    refine ⟨e0 ▸ isTan_mul (hu 0) h, ?_⟩
    rw [tcoord_congr hx e0 _ (isTan_mul (hu 0) h), tcoord_mul hx (hu 0) h, e, Fin.sum_univ_succ]
end ReciprocityTheory.ChartRestriction.G.Chart
