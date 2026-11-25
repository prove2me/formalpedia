-- Prove2me | solution 1 for UnipMove.MajH.key_ineq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:40:53.342422+00:00
-- url     : https://prove2.me/submissions/9384c112-3384-4e22-bd37-d16cff64439a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_DotAddRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove UnipMove.MajH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds UnipMove.GraphH NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
namespace UnipMove.MajH
theorem _root_.solution {A Bn u w D ρ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ Bn) (hu0 : 0 ≤ u) (hw0 : 0 ≤ w)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hu : u ≤ ρ * A) (hw : w ≤ ρ * Bn) (h1 : |D| ≤ u * Bn)
    (h2 : |D| ≤ A * w) :
    (1 - ρ) * (A ^ 2 + w ^ 2 + 2 * D + (u ^ 2 + Bn ^ 2 + 2 * D)) ≤
        (1 + ρ) * (A ^ 2 - u ^ 2 + Bn ^ 2 - w ^ 2) ∧
      (1 - ρ) * (A ^ 2 - u ^ 2 + Bn ^ 2 - w ^ 2) ≤
        (1 + ρ) * (A ^ 2 + w ^ 2 + 2 * D + (u ^ 2 + Bn ^ 2 + 2 * D)) := by
  have hD1 : |D| ≤ ρ * A * Bn := h1.trans (by nlinarith)
  have hD2 : |D| ≤ ρ * A * Bn := h2.trans (by nlinarith)
  have hAB : 2 * (A * Bn) ≤ A ^ 2 + Bn ^ 2 := by nlinarith [sq_nonneg (A - Bn)]
  have hu2 : u ^ 2 ≤ ρ ^ 2 * A ^ 2 := by nlinarith
  have hw2 : w ^ 2 ≤ ρ ^ 2 * Bn ^ 2 := by nlinarith
  have hDa := abs_le.1 hD1
  constructor
  · nlinarith [mul_nonneg hρ0.le hA, mul_nonneg (sub_nonneg.2 hρ1.le) hρ0.le]
  · have hsum : 2 * ρ * (A * Bn) + 2 * (u * w) ≤ ρ * (A ^ 2 + Bn ^ 2) + (u ^ 2 + w ^ 2) := by
      nlinarith [sq_nonneg (A - Bn), sq_nonneg (u - w)]
    have hkey : (1 + ρ) * (-D) ≤ ρ * (A * Bn) + u * w := by
      rcases le_or_gt (-D) 0 with hd | hd
      · nlinarith [mul_nonneg hA hB, mul_nonneg hu0 hw0]
      · have hd1 : -D ≤ u * Bn := (neg_le_abs D).trans h1
        have hd2 : -D ≤ A * w := (neg_le_abs D).trans h2
        have hdAB : -D ≤ ρ * (A * Bn) := by nlinarith [mul_le_mul_of_nonneg_right hu hB]
        have hAB0 : 0 < A * Bn := pos_of_mul_pos_right (by linarith : 0 < ρ * (A * Bn)) hρ0.le
        have hsq : (-D) * (-D) ≤ (u * Bn) * (A * w) := mul_le_mul hd1 hd2 hd.le (mul_nonneg hu0 hB)
        have hq : 0 ≤ (-D - ρ * (A * Bn)) * (-D - A * Bn) :=
          mul_nonneg_of_nonpos_of_nonpos (by linarith) (by nlinarith)
        have hmain : (A * Bn) * ((1 + ρ) * (-D)) ≤ (A * Bn) * (ρ * (A * Bn) + u * w) := by
          nlinarith
        exact le_of_mul_le_mul_left hmain hAB0
    nlinarith
end UnipMove.MajH
