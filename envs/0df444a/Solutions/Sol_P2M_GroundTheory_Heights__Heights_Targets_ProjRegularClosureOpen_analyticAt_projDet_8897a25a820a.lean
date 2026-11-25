-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjRegularClosureOpen_analyticAt_projDet_8897a25a820a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:40:25.622439+00:00
-- url     : https://prove2.me/submissions/acd751fb-cb58-4282-9c04-52bc2f0c404a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularClosureOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegularClosureOpen
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Targets.ProjRegularClosureOpen
namespace GroundTheory.Heights₂.Heights.Targets.ProjRegularClosureOpen
theorem _root_.solution {n : ℕ} {F : (Fin n → ℂ) → Fin (n + 1) → ℂ} {u : Fin n → ℂ}
    (hF : AnalyticAt ℂ F u) : AnalyticAt ℂ (fun v => F v 0 * (projNumMat F v).det) u := by
  have hc : ∀ i, AnalyticAt ℂ (fun v => F v i) u := fun i => analyticAt_pi_iff.1 hF i
  have hd : ∀ i (w : Fin n → ℂ), AnalyticAt ℂ (fun v => fderiv ℂ (fun v => F v i) v w) u :=
    fun i w => ((ContinuousLinearMap.apply ℂ ℂ w).analyticAt _).comp (hc i).fderiv
  have hm : ∀ i l, AnalyticAt ℂ (fun v => projNumMat F v i l) u := fun i l =>
    ((hc 0).mul (hd _ _)).sub ((hc _).mul (hd _ _))
  refine (hc 0).mul ?_
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact Finset.univ.analyticAt_fun_sum (fun σ _ =>
    analyticAt_const.mul (Finset.univ.analyticAt_fun_prod (fun i _ => hm _ _)))
end GroundTheory.Heights₂.Heights.Targets.ProjRegularClosureOpen
