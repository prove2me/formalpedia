-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KShort_norm_lt_of_mem_cube_d47b19df4675
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:01:25.663877+00:00
-- url     : https://prove2.me/submissions/7bba5787-89f5-4d17-a606-313556bdffe7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ShortVectors

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
open MeasureTheory Module Metric
noncomputable section
open GroundTheory.Heights₂.Heights.KShort
namespace GroundTheory.Heights₂.Heights.KShort
theorem _root_.solution {n : ℕ} (hn : 0 < n) {lam : ℝ} (hlam : 0 < lam)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ cube n (lam / √n)) : ‖x‖ < lam := by
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsq : (√(n : ℝ)) ^ 2 = n := Real.sq_sqrt (by positivity)
  have h1 : ∀ i, x i ^ 2 < (lam / √n) ^ 2 := fun i => by
    have := hx i
    have h0 : 0 ≤ |x i| := abs_nonneg _
    calc x i ^ 2 = |x i| ^ 2 := (sq_abs _).symm
      _ < (lam / √n) ^ 2 := by gcongr
  have hsum : ∑ i, x i ^ 2 < ∑ _i : Fin n, (lam / √n) ^ 2 :=
    Finset.sum_lt_sum_of_nonempty ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun i _ => h1 i
  have hsum' : ∑ _i : Fin n, (lam / √n) ^ 2 = lam ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, div_pow, hsq, nsmul_eq_mul]
    field_simp
  rw [EuclideanSpace.norm_eq]
  rw [Real.sqrt_lt' hlam]
  simpa [Real.norm_eq_abs, sq_abs, hsum'] using hsum
end GroundTheory.Heights₂.Heights.KShort
