-- Prove2me | solution 1 for PI.RhsWLim.W.phiT_strict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:34:07.554004+00:00
-- url     : https://prove2.me/submissions/cf695f0c-c33d-42a1-9c27-63f3b1f593bf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PhiDiff
import Theorems.Thm_PI_RhsWLim_W_mulVec_base
import Theorems.Thm_PI_RhsWLim_W_opGen_y
import Theorems.Thm_PI_RhsWLim_W_opGen_c
import Theorems.Thm_PI_RhsWLim_W_psiV_strict
import Theorems.Thm_PI_RhsWLim_W_dpsi_apply
import Theorems.Thm_PI_RhsWLim_W_DL_apply
import Theorems.Thm_PI_RhsWLim_W_phiT_coord_c
import Theorems.Thm_PI_RhsWLim_W_psiV_last_zero
import Theorems.Thm_PI_RhsWLim_W_beta_re_im
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.RhsWLim.W.DL_apply

set_option autoImplicit false
noncomputable section
open Matrix NormedSpace
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (T' : ℝ) (hT : 0 < T') : HasStrictFDerivAt (phiT k r T') (DL k T') 0 := by
  have hp := psiV_strict (k := k) (r := r) T'
  refine (hasStrictFDerivAt_piLp 2).2 fun o => ?_
  rcases o with _ | ⟨a, b⟩
  · have hs : ((Real.sqrt T' : ℝ) : ℂ) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.2 (Real.sqrt_pos.2 hT)
    have hlog := ((Complex.hasStrictDerivAt_log hs).hasStrictFDerivAt).restrictScalars ℝ
    rw [← psiV_last_zero (k := k) (r := r)] at hlog
    have H := Complex.imCLM.hasStrictFDerivAt.comp (0 : TrE k)
      (hlog.comp (0 : TrE k) ((ContinuousLinearMap.proj (R := ℝ) (wI k r (Fin.last k))).hasStrictFDerivAt.comp
        (0 : TrE k) hp))
    have hf : (fun x => phiT k r T' x none) =
        Complex.imCLM ∘ Complex.log ∘ (fun f : Fin (2 * r + k + 1) → ℂ => f (wI k r (Fin.last k))) ∘ psiV k r T' := by
      funext x; exact phiT_coord_c T' x
    rw [hf]
    refine H.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
    have hsq : (Real.sqrt T' : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; positivity
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.proj_apply,
      opGenL_apply, mvL_apply, mulVec_base, opGen_c, psiV_last_zero, Complex.imCLM_apply, PiLp.proj_apply,
      DL_apply, dgn, one_mul, smul_eq_mul]
    have : (Real.sqrt T' : ℂ) * ((q none : ℂ) * Complex.I) * (Real.sqrt T' : ℂ)⁻¹ = (q none : ℂ) * Complex.I := by
      field_simp
    rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, this]; simp
  · have Hj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * r + k + 1) => ℂ)
      (wI k r a.castSucc)).hasStrictFDerivAt.comp (0 : TrE k) hp
    cases b
    · have H := Complex.reCLM.hasStrictFDerivAt.comp (0 : TrE k) Hj
      refine H.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, dpsi_apply, opGen_y,
        beta_re_im, Complex.reCLM_apply, PiLp.proj_apply, DL_apply, dgn]
      change ((opGen k r q *ᵥ opBase k r T') (wI k r a.castSucc)).re = _
      rw [mulVec_base, opGen_y, beta_re_im]
      simp
    · have H := Complex.imCLM.hasStrictFDerivAt.comp (0 : TrE k) Hj
      refine H.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, dpsi_apply, opGen_y,
        beta_re_im, Complex.imCLM_apply, PiLp.proj_apply, DL_apply, dgn]
      change ((opGen k r q *ᵥ opBase k r T') (wI k r a.castSucc)).im = _
      rw [mulVec_base, opGen_y, beta_re_im]
      simp
end PI.RhsWLim.W
