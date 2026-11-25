-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.good_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:41:05.255571+00:00
-- url     : https://prove2.me/submissions/a222d22f-163b-4e0f-9bdc-e7bdbc43684b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SCWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_DivPowInteg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXEqRename
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_good_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_good_prod

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution (E0 : AA k d) {r : ℕ} (a : Fin r → Module.End k (AA k d))
    (ha : ∀ i X, GoodE R E0 X → GoodE R E0 (a i X)) (e : Fin r → ℕ) :
    ∀ X, GoodE R E0 X → GoodE R E0 ((List.ofFn fun i => a i ^ e i).prod X) := by
  refine good_prod E0 _ ?_
  intro T hT
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hT
  exact good_pow E0 (a i) (ha i) (e i)
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
