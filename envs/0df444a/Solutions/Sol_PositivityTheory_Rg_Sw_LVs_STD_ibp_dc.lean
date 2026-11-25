-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.STD.ibp_dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:48:57.596006+00:00
-- url     : https://prove2.me/submissions/2dc8c920-596f-40c4-ac66-eaf87d516baa

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffB
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_integrable_mul_of_contOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw.LVs.STD
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.STD
theorem _root_.solution {U : Set (Vr n)} (hU : IsOpen U) {F φ : Vr n → ℂ} (hF : ContDiffOn ℝ ∞ F U)
    (hφ : IsT U φ) (a : Fin n × Fin n) :
    ∫ x, F x * dc a φ x = - ∫ x, dc a F x * φ x := by
  have hFd : ∀ x ∈ tsupport φ, DifferentiableAt ℝ F x := fun x hx =>
    (hF.contDiffAt (hU.mem_nhds (hφ.sub hx))).differentiableAt (by simp)
  have hφd : ∀ x ∈ tsupport F, DifferentiableAt ℝ φ x := fun x _ =>
    (hφ.smooth.differentiable (by simp)) x
  have hFc : ContinuousOn (fun x => fderiv ℝ F x) U := hF.continuousOn_fderiv_of_isOpen hU (by simp)
  have hφc : Continuous (fun x => fderiv ℝ φ x) := hφ.smooth.continuous_fderiv (by simp)
  have hA : ∀ v : Vr n, Integrable (fun x => fderiv ℝ F x v * φ x) := fun v =>
    integrable_mul_of_contOn hU (hFc.clm_apply continuousOn_const) hφ.smooth.continuous hφ.cpt hφ.sub
  have hB : ∀ v : Vr n, Integrable (fun x => F x * fderiv ℝ φ x v) := fun v =>
    integrable_mul_of_contOn hU hF.continuousOn (hφc.clm_apply continuous_const)
      (hφ.cpt.fderiv_apply ℝ v)
      ((closure_minimal (fun x hx => support_fderiv_subset ℝ
        (fun h0 => (Function.mem_support.mp hx) (by simp [h0])))
        (isClosed_tsupport φ)).trans hφ.sub)
  have key : ∀ v : Vr n, ∫ x, F x * fderiv ℝ φ x v = - ∫ x, fderiv ℝ F x v * φ x := fun v =>
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hA v) (hB v)
      (integrable_mul_of_contOn hU hF.continuousOn hφ.smooth.continuous hφ.cpt hφ.sub) hFd hφd
  have e1 : ∫ x, F x * dc a φ x
      = (∫ x, F x * fderiv ℝ φ x (v1 a.1 a.2)) + Complex.I * ∫ x, F x * fderiv ℝ φ x (v2 a.1 a.2) := by
    rw [← integral_const_mul, ← integral_add (hB _) ((hB _).const_mul _)]
    congr 1
    funext x
    simp only [dc]
    ring
  have e2 : ∫ x, dc a F x * φ x
      = (∫ x, fderiv ℝ F x (v1 a.1 a.2) * φ x) + Complex.I * ∫ x, fderiv ℝ F x (v2 a.1 a.2) * φ x := by
    rw [← integral_const_mul, ← integral_add (hA _) ((hA _).const_mul _)]
    congr 1
    funext x
    simp only [dc]
    ring
  rw [e1, e2, key, key]
  ring
end PositivityTheory.Rg.Sw.LVs.STD
