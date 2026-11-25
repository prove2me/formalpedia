-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.valOver_vK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:59:23.319675+00:00
-- url     : https://prove2.me/submissions/43b50402-302e-4d06-a767-de7304d12711

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenVal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasVal_unique


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
open ReciprocityTheory.ChartRestriction.G.DVR
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
theorem _root_.solution (hϖ : Irreducible ϖ) : ValOver ϖ (FractionRing V) (vK hϖ) := by
  intro c n hc
  have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hϖ.ne_zero
  have hc0 : c ≠ 0 := by
    obtain ⟨u, hu⟩ := hc
    rw [hu]
    refine mul_ne_zero (zpow_ne_zero _ hπ) ?_
    exact (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr u.ne_zero
  change vK hϖ c = _
  simp only [vK, AddValuation.of_apply, if_neg hc0]
  rw [hasVal_unique hϖ (hasVal_valE hϖ hc0) hc]
end ReciprocityTheory.ChartRestriction.G.DVR.TG
