-- Prove2me | solution 1 for SNumbers.norm_projFin_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:09:08.149119+00:00
-- url     : https://prove2.me/submissions/98716471-2f8f-4042-9a17-3bf1ee62cde3

module
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Theorems.Thm_SNumbers_padFin_apply
attribute [local simp] SNumbers.padFin_apply

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SNumbers
theorem _root_.solution (h : n ≤ m) (x : PiLp p (fun _ : Fin m => 𝕜)) :
    ‖projFin (p := p) h x‖ ≤ ‖x‖ := by
  rcases p.dichotomy with (rfl | hp)
  · rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_ciSup]
    rcases isEmpty_or_nonempty (Fin n) with _ | _
    · rw [Real.iSup_of_isEmpty]
      exact Real.iSup_nonneg fun i => norm_nonneg _
    · refine ciSup_le fun j => ?_
      simpa [projFin_apply] using le_ciSup (Finite.bddAbove_range fun i => ‖x i‖) (Fin.castLE h j)
  · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
    rw [PiLp.norm_eq_sum hp0, PiLp.norm_eq_sum hp0]
    apply Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _) _
      (one_div_nonneg.mpr hp0.le)
    simp only [projFin_apply]
    have himg : ∑ j : Fin n, ‖x (Fin.castLE h j)‖ ^ p.toReal
        = ∑ i ∈ Finset.univ.image (Fin.castLE h), ‖x i‖ ^ p.toReal := by
      rw [Finset.sum_image fun a _ b _ hab => Fin.castLE_injective h hab]
    rw [himg]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => Real.rpow_nonneg (norm_nonneg _) _)
end SNumbers
