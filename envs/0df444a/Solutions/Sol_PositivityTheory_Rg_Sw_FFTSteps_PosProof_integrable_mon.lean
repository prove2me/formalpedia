-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.integrable_mon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:56.873195+00:00
-- url     : https://prove2.me/submissions/60611d97-b7ce-437d-aedd-efc43d01758b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousPhi
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralMonSelf
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_mon_prod
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_integrable_hk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.PosProof
variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof
theorem _root_.solution (m m' : Sg ι A B →₀ ℕ) :
    Integrable (fun z : Sg ι A B → ℂ => mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ))) := by
  simp_rw [mon_prod]
  have := Integrable.fintype_prod (f := fun s => hk (m s) (m' s)) (μ := fun _ => (volume : Measure ℂ))
    (fun s => integrable_hk _ _)
  rwa [← volume_pi] at this
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
