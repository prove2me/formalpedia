-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__rows_num_l_c160d0e13346
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:30:53.254724+00:00
-- url     : https://prove2.me/submissions/7cee7956-5da9-4171-8ee6-cd4c97d62320

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsNum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.MainNotions.BridgeLemma₂
private theorem pow_rpow_eq_rpow_mul {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (z : ℝ) :
    (x ^ n) ^ z = x ^ ((n : ℝ) * z) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
end Formalism.MainNotions.BridgeLemma₂
end

set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution {P σ h cr Γ a2 dq : ℝ} (hP : 1 ≤ P) (hσ : 1 ≤ σ) (h1 : 1 ≤ h) (hh : h ≤ P * σ ^ 4)
    (hcr : 0 ≤ cr) (hΓ : 0 ≤ Γ) :
    (h ^ cr) ^ 2 * (Γ * σ ^ a2) * σ ^ (-dq) ≤ (P ^ cr) ^ 2 * Γ * σ ^ (8 * cr + a2 - dq) := by
  have hσ0 : 0 < σ := by linarith
  have hP0 : 0 < P := by linarith
  have hh0 : 0 ≤ h := by linarith
  have key : h ^ cr ≤ P ^ cr * σ ^ (4 * cr) := by
    calc h ^ cr ≤ (P * σ ^ 4) ^ cr := Real.rpow_le_rpow hh0 hh hcr
      _ = P ^ cr * (σ ^ 4) ^ cr := Real.mul_rpow hP0.le (pow_nonneg hσ0.le 4)
      _ = P ^ cr * σ ^ (4 * cr) := by rw [pow_rpow_eq_rpow_mul hσ0.le]; norm_num
  have hsq : (h ^ cr) ^ 2 ≤ (P ^ cr * σ ^ (4 * cr)) ^ 2 := by
    rw [sq, sq]
    exact mul_le_mul key key (Real.rpow_nonneg hh0 _) (le_trans (Real.rpow_nonneg hh0 _) key)
  have e : σ ^ (8 * cr + a2 - dq) = σ ^ (4 * cr) * σ ^ (4 * cr) * σ ^ a2 * σ ^ (-dq) := by
    rw [← Real.rpow_add hσ0, ← Real.rpow_add hσ0, ← Real.rpow_add hσ0]
    congr 1
    ring
  have hnn : 0 ≤ Γ * σ ^ a2 * σ ^ (-dq) :=
    mul_nonneg (mul_nonneg hΓ (Real.rpow_nonneg hσ0.le _)) (Real.rpow_nonneg hσ0.le _)
  calc (h ^ cr) ^ 2 * (Γ * σ ^ a2) * σ ^ (-dq) = (h ^ cr) ^ 2 * (Γ * σ ^ a2 * σ ^ (-dq)) := by ring
    _ ≤ (P ^ cr * σ ^ (4 * cr)) ^ 2 * (Γ * σ ^ a2 * σ ^ (-dq)) := mul_le_mul_of_nonneg_right hsq hnn
    _ = (P ^ cr) ^ 2 * Γ * σ ^ (8 * cr + a2 - dq) := by rw [e]; ring
end Formalism.MainNotions.BridgeLemma₂
