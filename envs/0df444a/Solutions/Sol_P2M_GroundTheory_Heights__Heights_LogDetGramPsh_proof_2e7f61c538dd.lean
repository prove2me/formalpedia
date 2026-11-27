-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogDetGramPsh_proof_2e7f61c538dd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:03:25.804708+00:00
-- url     : https://prove2.me/submissions/43570963-ccac-4690-9187-6e2859a02b4f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PLogDetGramPsh
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_circleAverage_im_of_analytic_28853a1159d6


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix Metric Real MCPsh
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace LogDetGramPsh
theorem _root_.solution (hcont : LogDetGramContinuous.Statement)
    (hsub : LogDetGramSubmean.Statement) : LogDetGramPsh.Statement := by
  intro N g rk S
  have hYc : ContinuousOn (fun x => (S.τ x).map Complex.im) S.W :=
    continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k =>
      Complex.continuous_im.comp_continuousOn (S.τ_analytic j k).continuousOn
  have hFc : ContinuousOn S.f S.W :=
    continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k => (S.f_analytic j k).continuousOn
  have hc := hcont (Fin N → ℂ) S.W g rk (fun x => (S.τ x).map Complex.im) S.f hYc hFc
    S.im_posDef S.f_rank
  refine ⟨hc.upperSemicontinuousOn, ?_⟩
  intro z w hdisc
  have hline : ∀ ζ ∈ closedBall (0:ℂ) 1, z + ζ • w ∈ S.W := fun ζ hζ =>
    hdisc ζ (by simpa using hζ)
  have haff : ∀ ζ : ℂ, AnalyticAt ℂ (fun ζ : ℂ => z + ζ • w) ζ := fun ζ =>
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hτ : ∀ j k, AnalyticOnNhd ℂ (fun ζ : ℂ => S.τ (z + ζ • w) j k) (closedBall 0 1) :=
    fun j k ζ hζ => AnalyticAt.comp (g := fun x => S.τ x j k) (f := fun ζ : ℂ => z + ζ • w)
      (S.τ_analytic j k _ (hline ζ hζ)) (haff ζ)
  have hf : ∀ j k, AnalyticOnNhd ℂ (fun ζ : ℂ => S.f (z + ζ • w) j k) (closedBall 0 1) :=
    fun j k ζ hζ => AnalyticAt.comp (g := fun x => S.f x j k) (f := fun ζ : ℂ => z + ζ • w)
      (S.f_analytic j k _ (hline ζ hζ)) (haff ζ)
  have hYd : ContinuousOn (fun ζ : ℂ => (S.τ (z + ζ • w)).map Complex.im) (closedBall 0 1) :=
    continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k =>
      Complex.continuous_im.comp_continuousOn (hτ j k).continuousOn
  have hmean : ∀ j k, circleAverage (fun ζ : ℂ => (S.τ (z + ζ • w)).map Complex.im j k) 0 1 =
      (S.τ (z + (0:ℂ) • w)).map Complex.im j k := fun j k => by
    simpa only [map_apply] using circleAverage_im_of_analytic (hτ j k)
  obtain ⟨hint, hle⟩ := hsub g rk (fun ζ => (S.τ (z + ζ • w)).map Complex.im)
    (fun ζ => S.f (z + ζ • w)) (fun ζ hζ => S.im_posDef _ (hline ζ hζ)) hYd hmean hf
    (fun ζ hζ => S.f_rank _ (hline ζ hζ))
  refine ⟨hint, ?_⟩
  have e : z + (0:ℂ) • w = z := by simp
  simpa only [e] using hle
end LogDetGramPsh
end GroundTheory.Heights₂.Heights
