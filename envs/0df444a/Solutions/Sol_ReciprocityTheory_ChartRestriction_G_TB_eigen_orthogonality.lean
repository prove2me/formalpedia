-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.eigen_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:33:35.19807+00:00
-- url     : https://prove2.me/submissions/8e6833dd-300d-4253-8789-0c3aa812bb5b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_EigenLift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_EigenLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_beta_sesquilinear
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_betaH_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_betaH_smul_right

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ReciprocityTheory.ChartRestriction.G.TB
theorem _root_.solution : EigenOrthSt := by
  intro R _ d O _ _ k _ _ _ B χ χ' ξ η hξ hη ⟨a, ha⟩
  have h := beta_sesquilinear R d O k B a ξ η
  rw [hξ a, hη (star a), betaH_smul_left, betaH_smul_right] at h
  have h2 : (χ a - χ' (star a)) * betaH k ξ η = 0 := by rw [sub_mul, h, sub_self]
  exact ha.mul_right_eq_zero.mp h2
end ReciprocityTheory.ChartRestriction.G.TB
