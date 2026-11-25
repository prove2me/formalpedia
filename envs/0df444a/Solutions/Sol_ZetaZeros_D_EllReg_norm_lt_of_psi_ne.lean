-- Prove2me | solution 1 for ZetaZeros.D.EllReg.norm_lt_of_psi_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:02:39.533365+00:00
-- url     : https://prove2.me/submissions/12f55a62-ba52-4705-a47c-205a93bb51d2

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDecay
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDil
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDer
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_ExistsSmoothExt

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
namespace ZetaZeros.D.EllReg
theorem _root_.solution {d : ℕ} {ψ0 : E d → ℝ} (hψ0s : tsupport ψ0 ⊆ ball 0 2) {r : ℝ} (hr : 0 < r)
    {x x0 : E d} (hz : ψ0 (r⁻¹ • (x - x0)) ≠ 0) : ‖x - x0‖ < 2 * r := by
  have hmem : r⁻¹ • (x - x0) ∈ ball (0 : E d) 2 := hψ0s (subset_tsupport _ hz)
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr] at hmem
  rw [inv_mul_lt_iff₀ hr] at hmem
  linarith
end ZetaZeros.D.EllReg
