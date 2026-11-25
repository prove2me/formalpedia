-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.foldr_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:32:09.658696+00:00
-- url     : https://prove2.me/submissions/72f6b9be-78fb-4bcd-83a9-5a89b57a88be

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_WickFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXHasSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nablaL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.TB.SCPf.nablaL_apply

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution (f : ι → AA k d → AA k d) (F : ι → Module.End k (AA k d)) (hF : ∀ l, ⇑(F l) = f l)
    (n : ι →₀ ℕ) (L : List ι) (G : AA k d) :
    L.foldr (fun l g => (f l)^[n l] g) G = (L.map fun l => F l ^ n l).prod G := by
  induction L with
  | nil => simp
  | cons a L ih =>
    first
    | simp only [List.foldr_cons, List.map_cons, List.prod_cons, Module.End.mul_apply, Module.End.pow_apply, hF, ih]
    | simp only [List.foldr_cons, List.map_cons, List.prod_cons, LinearMap.mul_apply, LinearMap.pow_apply, hF, ih]
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
