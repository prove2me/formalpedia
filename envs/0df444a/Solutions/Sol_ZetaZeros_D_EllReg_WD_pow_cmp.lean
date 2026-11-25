-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WD.pow_cmp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:00:41.805606+00:00
-- url     : https://prove2.me/submissions/a61e4d6c-e9ac-4983-9f22-f6b3e0614303

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeightDiff

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
open ZetaZeros.D.EllReg.WD
variable {d : ℕ}
namespace ZetaZeros.D.EllReg.WD
theorem _root_.solution {X Y K : ℝ} (p : ℝ) (hX : 0 < X) (hY : 0 < Y) (hK : 1 ≤ K)
    (h1 : X ≤ K * Y) (h2 : Y ≤ K * X) : X ^ p ≤ K ^ |p| * Y ^ p := by
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  rcases le_or_gt 0 p with hp | hp
  · rw [abs_of_nonneg hp, ← Real.mul_rpow hK0.le hY.le]
    exact Real.rpow_le_rpow hX.le h1 hp
  · rw [abs_of_neg hp]
    have h3 : K⁻¹ * Y ≤ X := by
      calc K⁻¹ * Y ≤ K⁻¹ * (K * X) := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hK0.le)
        _ = X := by rw [← mul_assoc, inv_mul_cancel₀ hK0.ne', one_mul]
    have hKY : 0 < K⁻¹ * Y := mul_pos (inv_pos.2 hK0) hY
    have h4 : X ^ p ≤ (K⁻¹ * Y) ^ p := by
      exact Real.rpow_le_rpow_of_nonpos hKY h3 hp.le
    calc X ^ p ≤ (K⁻¹ * Y) ^ p := h4
      _ = K ^ (-p) * Y ^ p := by
        rw [Real.mul_rpow (inv_nonneg.2 hK0.le) hY.le, Real.inv_rpow hK0.le, ← Real.rpow_neg hK0.le]
end ZetaZeros.D.EllReg.WD
