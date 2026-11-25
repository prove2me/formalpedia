-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.ordGE_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:44:36.156513+00:00
-- url     : https://prove2.me/submissions/3e59856f-b3ef-482e-83aa-2fbfc4501e4d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChgPfTP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_ordGE_one_of_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_ordGE_finsuppProd

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
variable {k : Type} [CommRing k]
namespace ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
theorem _root_.solution {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ k) (ha : ∀ s, constantCoeff (a s) = 0)
    {r : ℕ} {g : MvPowerSeries σ k} (hg : OrdGE r g) : OrdGE r (subst a g) := by
  intro e he
  have hsub : MvPowerSeries.HasSubst a := (by first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero ha)
  rw [MvPowerSeries.coeff_subst hsub]
  refine finsum_eq_zero_of_forall_eq_zero fun dd => ?_
  by_cases hd : dd.degree < r
  · rw [hg dd hd, zero_smul]
  · rw [ordGE_finsuppProd a (fun s => ordGE_one_of_const (ha s)) dd e (by omega), smul_zero]
end ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
