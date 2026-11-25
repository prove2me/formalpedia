-- Prove2me | solution 1 for ZetaZeros.D.EllReg.pf_fourier_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:06:59.953368+00:00
-- url     : https://prove2.me/submissions/cd1960f6-66ce-4f28-8fee-be70ec9745a9

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_PairingFourier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {d : ℕ}
namespace ZetaZeros.D.EllReg
theorem _root_.solution (k : E d → ℂ) (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k) :
    Integrable (𝓕 k) := by
  have hdecay : ∀ m n : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ m * ‖iteratedFDeriv ℝ n k x‖ ≤ C := by
    intro m n
    have hcn : Continuous fun x => iteratedFDeriv ℝ n k x := by
      exact hk.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
    have hc : Continuous fun x : E d => ‖x‖ ^ m * ‖iteratedFDeriv ℝ n k x‖ :=
      (continuous_norm.pow m).mul hcn.norm
    have hs : HasCompactSupport fun x : E d => ‖x‖ ^ m * ‖iteratedFDeriv ℝ n k x‖ :=
      ((hkc.iteratedFDeriv (𝕜 := ℝ) n).norm).mul_left
    obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
    exact ⟨C, fun x => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC x)⟩
  let S : SchwartzMap (E d) ℂ := ⟨k, hk, hdecay⟩
  exact (SchwartzMap.fourierTransformCLM ℂ S).integrable
end ZetaZeros.D.EllReg
