-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hasFDerivAt_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:05:16.528178+00:00
-- url     : https://prove2.me/submissions/256ae1cb-86e9-4681-b25d-dcd73a6999ce

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrable_scaled

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Convolution
noncomputable section
variable {D : ℕ}
variable (ρ : Mollifier D)
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {ε : ℝ} (hε : 0 < ε) {g : (Fin D → ℂ) → F} (hcg : HasCompactSupport g) (hg : ContDiff ℝ 1 g)
    (x : Fin D → ℂ) :
    HasFDerivAt (fun x => ∫ t, ρ.scaled ε t • g (x - t))
      (∫ t, ρ.scaled ε t • fderiv ℝ g (x - t)) x := by
  have h := hcg.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    (integrable_scaled ρ hε).locallyIntegrable hg x
  have e1 : (ρ.scaled ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) =
      fun x => ∫ t, ρ.scaled ε t • g (x - t) := by
    funext y
    rw [convolution_def]
    rfl
  have e2 : (ρ.scaled ε ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR (Fin D → ℂ), volume]
      fderiv ℝ g) x = ∫ t, ρ.scaled ε t • fderiv ℝ g (x - t) := by
    rw [convolution_def]
    congr 1
  rw [e1, e2] at h
  exact h
end ReciprocityTheory.AnForm.A
