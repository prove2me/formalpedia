-- Prove2me | solution 1 for PositivityTheory.KReal.polChi_stable_second_action
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:41:24.883193+00:00
-- url     : https://prove2.me/submissions/11f9fc0c-2c11-45fe-8fa8-ba35d66ecb70

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm
import Theorems.Thm_PositivityTheory_KReal_fockAct1_fockAct2_commute


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
open Harm
variable {p q r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution (c : ℂ) (W : Mat r s) {g : Pol p q r s} (hg : g ∈ polChi p q r s c) :
    fockAct2 p q r s W g ∈ polChi p q r s c := by
  unfold polChi jointEig at *
  rw [Submodule.mem_iInf] at hg ⊢
  intro Z
  have h1 := hg Z
  rw [LinearMap.mem_ker] at h1 ⊢
  have hc := fockAct1_fockAct2_commute (p := p) (q := q) (r := r) (s := s) Z.1 W
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at h1 ⊢
  rw [← Module.End.mul_apply, hc, Module.End.mul_apply, ← map_smul, ← map_sub, h1, map_zero]
end PositivityTheory.KReal
