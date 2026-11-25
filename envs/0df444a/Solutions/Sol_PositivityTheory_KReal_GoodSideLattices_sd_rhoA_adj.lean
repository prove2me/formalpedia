-- Prove2me | solution 1 for PositivityTheory.KReal.GoodSideLattices.sd_rhoA_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:09:02.91588+00:00
-- url     : https://prove2.me/submissions/b5c23d51-b44f-4678-9cf4-3f25f8d751da

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreStar
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGen
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreSide
import Theorems.Thm_PositivityTheory_KReal_GoodSideLattices_sd_trace_Eab
import Theorems.Thm_PositivityTheory_KReal_GoodSideLattices_sd_sb_symm
import Theorems.Thm_PositivityTheory_KReal_GoodSideLattices_sd_rhoA_coe
import Theorems.Thm_PositivityTheory_KReal_adj2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
open PositivityTheory.KReal.GoodSideLattices
variable {p q r s : ℕ}
namespace PositivityTheory.KReal.GoodSideLattices
theorem _root_.solution (τ : ℂ) (τ0 : ℚ) (hτ : τ = τ0) (d : ℕ) : AdjK (sd_rhoA p q r s τ d) := by
  intro a b hab u v
  rw [Submodule.coe_inner, Submodule.coe_inner, sd_rhoA_coe τ d hab,
    sd_rhoA_coe τ d (sd_sb_symm hab), sd_fvTw_apply, sd_fvTw_apply, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, adj2 p q r s a b, sd_trace_Eab,
    sd_trace_Eab]
  by_cases h : a = b
  · subst h
    simp [epsB, hab, hτ]
  · simp [epsB, hab, hτ, h, Ne.symm h]
end PositivityTheory.KReal.GoodSideLattices
