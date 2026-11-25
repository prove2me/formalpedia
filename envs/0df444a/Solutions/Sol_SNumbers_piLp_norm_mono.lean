-- Prove2me | solution 1 for SNumbers.piLp_norm_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:24:00.203435+00:00
-- url     : https://prove2.me/submissions/1c35590a-99f4-48d3-8bbb-546c863341ca

module
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_PiLpCoordinates

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SNumbers
theorem _root_.solution {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, SeminormedAddCommGroup (β i)] {x y : PiLp p β}
    (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : ‖x‖ ≤ ‖y‖ := by
  rcases p.dichotomy with (rfl | hp)
  · rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_ciSup]
    exact ciSup_mono (Finite.bddAbove_range _) h
  · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
    rw [PiLp.norm_eq_sum hp0, PiLp.norm_eq_sum hp0]
    have hsum : (∑ i, ‖x i‖ ^ p.toReal) ≤ ∑ i, ‖y i‖ ^ p.toReal :=
      Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (norm_nonneg _) (h i) hp0.le
    exact Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
      hsum (one_div_nonneg.mpr hp0.le)
end SNumbers
