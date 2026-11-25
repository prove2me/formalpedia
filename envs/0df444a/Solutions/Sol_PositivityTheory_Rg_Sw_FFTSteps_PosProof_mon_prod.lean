-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.mon_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:53:07.853599+00:00
-- url     : https://prove2.me/submissions/edcb1569-965a-4a07-99c1-e3f284069d8c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousPhi
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralMonSelf
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_gw_prod

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
theorem _root_.solution (m m' : Sg ι A B →₀ ℕ) (z : Sg ι A B → ℂ) :
    mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) = ∏ s, hk (m s) (m' s) (z s) := by
  rw [gw_prod]
  simp only [mon, hk, Complex.star_def, map_prod, map_pow, Finset.prod_mul_distrib]
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
