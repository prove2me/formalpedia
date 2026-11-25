-- Prove2me | solution 1 for ZetaZeros.D.EllReg.pf_modulate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:07:01.931101+00:00
-- url     : https://prove2.me/submissions/72652e55-9368-4350-acac-79f00d0c515f

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_PairingFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {d : ℕ}
private theorem fourier_eq_integral_eF_mul (f : E d → ℂ) (ζ : E d) :
    𝓕 f ζ = ∫ x, eF ζ x * f x := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  try dsimp only
  rw [smul_eq_mul]
  unfold eF
  congr 1; congr 1; push_cast; ring
end
end ZetaZeros.D.EllReg
end

set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {d : ℕ}
namespace ZetaZeros.D.EllReg
theorem _root_.solution (b : E d → ℂ) (ξ ζ : E d) : 𝓕 (fun y => b y * eF ξ y) ζ = 𝓕 b (ζ + ξ) := by
  rw [fourier_eq_integral_eF_mul, fourier_eq_integral_eF_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  try dsimp only
  have h : eF ζ y * eF ξ y = eF (ζ + ξ) y := by
    simp only [eF, ← Complex.exp_add, inner_add_right]
    congr 1; push_cast; ring
  rw [← h]; ring
end ZetaZeros.D.EllReg
