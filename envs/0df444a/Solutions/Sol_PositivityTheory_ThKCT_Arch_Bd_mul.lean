-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.Bd.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:33.442012+00:00
-- url     : https://prove2.me/submissions/d8e94d84-387f-4fe1-b79d-95ee2a0a4708

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
import Theorems.Thm_PositivityTheory_ThKCT_Arch_Bd_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Arch
open scoped ContDiff NNReal
open Complex Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace PositivityTheory.ThKCT.Arch
namespace Bd
theorem _root_.solution {m r : ℕ} {a f : V → ℂ} (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) {A C : ℝ}
    (hA : ∀ i ≤ m, ∀ x, ‖iteratedFDeriv ℝ i a x‖ ≤ A * (1 + ‖x‖) ^ r) (h : Bd (m + r) f C) :
    Bd m (fun x => a x * f x) (2 ^ m * (A * C)) := by
  intro j hj x
  have hA0 : 0 ≤ A := by
    have := (norm_nonneg _).trans (hA 0 (Nat.zero_le _) 0)
    simpa using this
  have h1 := norm_iteratedFDeriv_mul_le ha hf x (n := j) (by exact_mod_cast le_top)
  refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans ?_
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum (g := fun i => (j.choose i : ℝ) * (A * C)) fun i hi => ?_).trans ?_
  · have hi' := Finset.mem_range.1 hi
    have h2 := h (j - i) (by omega) x
    have h3 := hA i (by omega) x
    calc _ = (j.choose i : ℝ) * (‖iteratedFDeriv ℝ i a x‖ * ((1 + ‖x‖) ^ m * ‖iteratedFDeriv ℝ (j - i) f x‖)) := by ring
      _ ≤ (j.choose i : ℝ) * ((A * (1 + ‖x‖) ^ r) * ((1 + ‖x‖) ^ m * ‖iteratedFDeriv ℝ (j - i) f x‖)) := by gcongr
      _ = (j.choose i : ℝ) * (A * ((1 + ‖x‖) ^ (m + r) * ‖iteratedFDeriv ℝ (j - i) f x‖)) := by ring
      _ ≤ _ := by gcongr
  · rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hA0 h.nonneg)
    push_cast
    exact pow_le_pow_right₀ one_le_two hj
end Bd
end PositivityTheory.ThKCT.Arch
