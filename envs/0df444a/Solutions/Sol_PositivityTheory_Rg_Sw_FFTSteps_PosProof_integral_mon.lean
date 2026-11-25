-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.integral_mon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:13.825847+00:00
-- url     : https://prove2.me/submissions/43937d10-64a5-4dfe-8946-e639664976f5

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousPhi
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralMonSelf
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_mon_prod

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
    ∫ z : Sg ι A B → ℂ, mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) =
      ∏ s, ∫ w, hk (m s) (m' s) w := by
  simp_rw [mon_prod]
  exact integral_fintype_prod_volume_eq_prod (fun s w => hk (m s) (m' s) w)
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
