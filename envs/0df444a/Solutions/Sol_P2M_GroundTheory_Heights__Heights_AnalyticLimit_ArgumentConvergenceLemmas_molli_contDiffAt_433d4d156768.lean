-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_molli_contDiffAt_433d4d156768
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:43:22.391783+00:00
-- url     : https://prove2.me/submissions/07e0f9cc-73e0-498a-9bcf-a90e183d14b8

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_RegularizedMaxC2ExampleRealLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_NormIteratedFDerivCompLeOfIsOpen
import Theorems.Thm_ReciprocityTheory_AnForm_A_exists_thick
import Theorems.Thm_ReciprocityTheory_AnForm_A_molli_eq_C
import Theorems.Thm_ReciprocityTheory_AnForm_A_scaled_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_scaled_hasCompactSupport


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open GroundTheory.Heights₂.Heights.AnalyticLimit.ArgumentConvergenceLemmas
open Filter Topology Metric Set MeasureTheory
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli shrink)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (errE errorWithLinear ell)
noncomputable section
namespace GroundTheory.Heights₂.Heights.AnalyticLimit.ArgumentConvergenceLemmas
theorem _root_.solution {D : ℕ} (ρ : Mollifier D) {P : Set (Fin D → ℂ)} (hP : IsOpen P)
    {u : (Fin D → ℂ) → ℝ} (hu : ContinuousOn u P) {ε : ℝ} (hε : 0 < ε) {z : Fin D → ℂ}
    (hz : z ∈ shrink P ε) : ContDiffAt ℝ ∞ (molli ρ ε u) z := by
  obtain ⟨δ, hδ, hδP⟩ := ReciprocityTheory.AnForm.A.exists_thick hP hε.le hz
  have hi : Integrable ((closedBall z (ε + δ)).indicator u) :=
    (integrable_indicator_iff isClosed_closedBall.measurableSet).2
      ((hu.mono hδP).integrableOn_compact (isCompact_closedBall z (ε + δ)))
  have hg := (ReciprocityTheory.AnForm.A.scaled_hasCompactSupport ρ hε).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) (n := ⊤) (ReciprocityTheory.AnForm.A.scaled_contDiff ρ ε)
    hi.locallyIntegrable
  refine hg.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds z hδ] with y hy
  rw [mem_ball] at hy
  rw [ReciprocityTheory.AnForm.A.molli_eq_C ρ hε (C := closedBall z (ε + δ))
    (closedBall_subset_closedBall' (by linarith)), convolution_def]
  rfl
end GroundTheory.Heights₂.Heights.AnalyticLimit.ArgumentConvergenceLemmas
