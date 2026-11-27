-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedTopAlgebra_proof_e2ad6d18b80c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:57:48.948873+00:00
-- url     : https://prove2.me/submissions/38822603-535d-4434-a660-f59083e5b412

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsMixedTopAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPolyNonnegAtZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedTopAlgebra
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedTopAlgebra_clear_den_607802cc90d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedTopAlgebra_sum_ge_39d70bd0cb3e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Filter Polynomial
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace MixedTopAlgebra
theorem _root_.solution (hP : PolyNonnegAtZero.Statement) : MixedTopAlgebra.Statement := by
  intro d m hd hm hmd hST
  set P : Polynomial ℝ := ∑ i ∈ Finset.range (d + 1), C ((d.choose i : ℝ) * m i) * X ^ i with hPdef
  have heval : ∀ t : ℝ, P.eval t = ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * m i * t ^ i := by
    intro t; simp [P, eval_finsetSum]
  have h0 : P.eval 0 = m 0 := by
    rw [heval, Finset.sum_eq_single 0]
    · simp
    · intro i _ hi; simp [zero_pow hi]
    · intro h; simp at h
  rw [← h0]
  refine hP d P (m d) hmd ?_ ?_
  · intro t ht hPt
    obtain ⟨p, hp⟩ : ∃ p : ℕ, (p : ℤ) = t.num :=
      ⟨t.num.toNat, Int.toNat_of_nonneg (Rat.num_nonneg.mpr ht.le)⟩
    have hp1 : 1 ≤ p := by
      have : 0 < t.num := Rat.num_pos.mpr ht
      omega
    have hq0 : (0 : ℝ) < (t.den : ℝ) := by exact_mod_cast t.den_pos
    have htq : (t : ℝ) = (p : ℝ) / (t.den : ℝ) := by
      rw [Rat.cast_def, ← hp]; push_cast; rfl
    have hS := MixedTopAlgebra.clear_den d m (t.den : ℝ) (p : ℝ) hq0.ne'
    rw [← htq, ← heval] at hS
    have hSpos : 0 < ∑ i ∈ Finset.range (d + 1),
        (d.choose i : ℝ) * (t.den : ℝ) ^ (d - i) * (p : ℝ) ^ i * m i := by
      rw [← hS]; positivity
    have hT := hST t.den p t.den_pos hp1 hSpos
    have hge := MixedTopAlgebra.sum_ge d m hm (t.den : ℝ) (p : ℝ) hq0.le (by positivity)
    have hqd : (0 : ℝ) < (t.den : ℝ) ^ d := by positivity
    have hmt : (t.den : ℝ) ^ d * (m d * (t : ℝ) ^ d) = (p : ℝ) ^ d * m d := by
      rw [htq, div_pow]; field_simp
    refine le_of_mul_le_mul_left ?_ hqd
    rw [hmt, hS]
    nlinarith [mul_nonneg hq0.le hT]
  · have hlow : ∀ t : ℝ, 0 ≤ t → m 0 + m d * t ^ d ≤ P.eval t := by
      intro t ht
      have hsub : ({0, d} : Finset ℕ) ⊆ Finset.range (d + 1) := by
        intro i hi; simp at hi; simp; omega
      rw [heval]
      calc m 0 + m d * t ^ d = ∑ i ∈ ({0, d} : Finset ℕ), (d.choose i : ℝ) * m i * t ^ i := by
            rw [Finset.sum_pair (by omega)]; simp
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun i hi hi' => by
            have h1 : 1 ≤ i := by simp at hi'; omega
            have := hm i h1 (by simp at hi; omega)
            positivity
    filter_upwards [eventually_ge_atTop (max 1 ((|m 0| + 1) / m d))] with t ht
    have ht1 : 1 ≤ t := le_of_max_le_left ht
    have ht2 : (|m 0| + 1) / m d ≤ t := le_of_max_le_right ht
    have htd : t ≤ t ^ d := by
      calc t = t ^ 1 := (pow_one t).symm
        _ ≤ t ^ d := pow_le_pow_right₀ ht1 (by omega)
    have h3 : |m 0| + 1 ≤ m d * t := by rw [div_le_iff₀ hmd] at ht2; linarith
    have h4 : m d * t ≤ m d * t ^ d := mul_le_mul_of_nonneg_left htd hmd.le
    have h5 := hlow t (by linarith)
    linarith [neg_abs_le (m 0)]
end MixedTopAlgebra
end GroundTheory.Heights₂.Heights.HilbertSamuel
