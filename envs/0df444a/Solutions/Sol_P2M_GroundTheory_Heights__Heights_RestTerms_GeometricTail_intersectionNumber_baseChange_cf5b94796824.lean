-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_GeometricTail_intersectionNumber_baseChange_cf5b94796824
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:51:08.331482+00:00
-- url     : https://prove2.me/submissions/e1c192dd-bb26-4df3-8fd4-728b66777761

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace GeometricTail
theorem _root_.solution : GeometricTail.Statement := by
  intro p k hp hk
  set x : ℝ := (p ^ k)⁻¹ with hx
  have hpk : (2 : ℝ) ≤ p ^ k := by
    calc (2 : ℝ) ≤ p := hp
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := pow_le_pow_right₀ (by linarith) hk
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ≤ 1 / 2 := by
    rw [hx]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hterm : ∀ n : ℕ, (p ^ ((n + 1) * k))⁻¹ = x * x ^ n := by
    intro n
    rw [hx, ← pow_succ', inv_pow, ← pow_mul, mul_comm k]
  have hs : Summable (fun n : ℕ => x ^ n) :=
    summable_geometric_of_lt_one hx0 (by linarith)
  refine ⟨?_, ?_⟩
  · simp_rw [hterm]
    exact hs.mul_left x
  · simp_rw [hterm]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hx0 (by linarith)]
    have h1 : (1 - x)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    calc x * (1 - x)⁻¹ ≤ x * 2 := mul_le_mul_of_nonneg_left h1 hx0
      _ = 2 * x := by ring
end GeometricTail
end GroundTheory.Heights₂.Heights.RestTerms
