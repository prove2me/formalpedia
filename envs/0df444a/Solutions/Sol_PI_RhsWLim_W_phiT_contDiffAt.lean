-- Prove2me | solution 1 for PI.RhsWLim.W.phiT_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:29:26.408354+00:00
-- url     : https://prove2.me/submissions/0f1645af-0e7e-4070-981b-ffa7fae491b9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PhiDiff
import Theorems.Thm_PI_RhsWLim_W_psiV_contDiffAt
import Theorems.Thm_PI_RhsWLim_W_phiT_coord_c
import Theorems.Thm_PI_RhsWLim_W_psiV_last_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NormedSpace
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (T' : ℝ) (hT : 0 < T') : ContDiffAt ℝ 1 (phiT k r T') 0 := by
  have hp := psiV_contDiffAt (k := k) (r := r) T'
  refine (contDiffAt_piLp 2).2 fun o => ?_
  rcases o with _ | ⟨a, b⟩
  · have hlog : ContDiffAt ℝ 1 Complex.log (psiV k r T' 0 (wI k r (Fin.last k))) := by
      rw [psiV_last_zero]
      exact (Complex.contDiffAt_log (Complex.ofReal_mem_slitPlane.2 (Real.sqrt_pos.2 hT))).restrict_scalars ℝ
    have := Complex.imCLM.contDiff.contDiffAt.comp (0 : TrE k)
      (hlog.comp (0 : TrE k) ((ContinuousLinearMap.proj (R := ℝ) (wI k r (Fin.last k))).contDiff.contDiffAt.comp
        (0 : TrE k) hp))
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
    exact phiT_coord_c T' q
  · have hj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * r + k + 1) => ℂ)
      (wI k r a.castSucc)).contDiff.contDiffAt.comp (0 : TrE k) hp
    cases b
    · exact Complex.reCLM.contDiff.contDiffAt.comp (0 : TrE k) hj
    · exact Complex.imCLM.contDiff.contDiffAt.comp (0 : TrE k) hj
end PI.RhsWLim.W
