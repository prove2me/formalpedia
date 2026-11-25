-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.integral_mon_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:23:06.897423+00:00
-- url     : https://prove2.me/submissions/21ebc34a-e7c0-422c-8c43-b7ec120e0e08

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousPhi
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralMonSelf
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_integral_mon
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_integral_hk_ne


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
theorem _root_.solution (m m' : Sg ι A B →₀ ℕ) (h : m ≠ m') :
    ∫ z : Sg ι A B → ℂ, mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) = 0 := by
  rw [integral_mon]
  obtain ⟨s, hs⟩ : ∃ s, m s ≠ m' s := by
    by_contra hc
    push Not at hc
    exact h (Finsupp.ext hc)
  exact Finset.prod_eq_zero (Finset.mem_univ s) (integral_hk_ne _ _ hs)
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
