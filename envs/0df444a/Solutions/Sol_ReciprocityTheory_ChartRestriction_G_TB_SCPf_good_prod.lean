-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.good_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:32:16.16738+00:00
-- url     : https://prove2.me/submissions/5d15420d-c938-4f60-890a-95e5ec63a706

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SCWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_DivPowInteg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXEqRename
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
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution (E0 : AA k d) (L : List (Module.End k (AA k d)))
    (hL : ∀ T ∈ L, ∀ X, GoodE R E0 X → GoodE R E0 (T X)) : ∀ X, GoodE R E0 X → GoodE R E0 (L.prod X) := by
  induction L with
  | nil =>
    intro X hX
    rw [List.prod_nil]
    exact hX
  | cons T L ih =>
    intro X hX
    rw [List.prod_cons]
    exact hL T (by simp) _ (ih (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT')) X hX)
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
