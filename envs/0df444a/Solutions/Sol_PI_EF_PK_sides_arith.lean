-- Prove2me | solution 1 for PI.EF.PK.sides_arith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:36:57.108829+00:00
-- url     : https://prove2.me/submissions/d2211917-9863-4a99-8cd3-fd71f29061e5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronTruncOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ContinuousInvSqrt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real
namespace PI.EF.PK
theorem _root_.solution {C1 C2 u T T' c l1 l2 as large₂ lNu uc : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hT0 : 0 < T)
    (hu0 : 0 < u) (hTu : T ≤ u) (hTT' : T ≤ T') (hc1 : 1 < c) (hc3 : c ≤ 3) (huc0 : 0 ≤ uc)
    (huc : uc ≤ 3 * u)
    (hLg0 : 0 ≤ large₂) (hl1 : l1 ≤ large₂) (hl1' : 0 ≤ l1) (hl2 : l2 ≤ 2 * large₂) (has : as ≤ 2 * large₂)
    (has0 : 0 ≤ as) (hlNu : 0 ≤ lNu) :
    C1 * l1 ^ 2 * (uc / T') * (c - -1 / 2) + C1 * l1 ^ 2 * (uc / T') * (c - -1 / 2) +
      C2 * l2 * (2 * as) ≤ (21 * C1 + 8 * C2) * (u * large₂ ^ 2 / T + lNu) := by
  have hT'0 : 0 < T' := by linarith
  have hq : uc / T' ≤ 3 * u / T := by
    rw [div_le_div_iff₀ hT'0 hT0]
    nlinarith
  have hl1sq : l1 ^ 2 ≤ large₂ ^ 2 := by nlinarith
  have hcc : c - -1 / 2 ≤ 7 / 2 := by linarith
  have hcc0 : 0 ≤ c - -1 / 2 := by linarith
  have hq0 : 0 ≤ uc / T' := div_nonneg huc0 hT'0.le
  have hY0 : 0 ≤ C1 * large₂ ^ 2 * (3 * u / T) :=
    mul_nonneg (mul_nonneg hC1 (sq_nonneg _)) (div_nonneg (by linarith) hT0.le)
  have hX : C1 * l1 ^ 2 * (uc / T') ≤ C1 * large₂ ^ 2 * (3 * u / T) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hl1sq hC1) hq hq0 (mul_nonneg hC1 (sq_nonneg _))
  have hA : C1 * l1 ^ 2 * (uc / T') * (c - -1 / 2) ≤ C1 * large₂ ^ 2 * (3 * u / T) * (7 / 2) :=
    mul_le_mul hX hcc hcc0 hY0
  have hB : C2 * l2 * (2 * as) ≤ C2 * (2 * large₂) * (2 * (2 * large₂)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hl2 hC2) (by linarith) (by linarith)
      (mul_nonneg hC2 (by linarith))
  have e1 : C1 * large₂ ^ 2 * (3 * u / T) * (7 / 2) = 21 / 2 * (C1 * (u * large₂ ^ 2 / T)) := by ring
  have e2 : C2 * (2 * large₂) * (2 * (2 * large₂)) = 8 * (C2 * large₂ ^ 2) := by ring
  have h3 : large₂ ^ 2 ≤ u * large₂ ^ 2 / T := by
    rw [le_div_iff₀ hT0]
    nlinarith [sq_nonneg large₂]
  have h4 : C2 * large₂ ^ 2 ≤ C2 * (u * large₂ ^ 2 / T) := mul_le_mul_of_nonneg_left h3 hC2
  have h5 : 0 ≤ (21 * C1 + 8 * C2) * lNu := mul_nonneg (by linarith) hlNu
  have e3 : (21 * C1 + 8 * C2) * (u * large₂ ^ 2 / T + lNu) =
      21 * (C1 * (u * large₂ ^ 2 / T)) + 8 * (C2 * (u * large₂ ^ 2 / T)) + (21 * C1 + 8 * C2) * lNu := by ring
  rw [e3]
  linarith
end PI.EF.PK
