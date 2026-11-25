-- Prove2me | solution 1 for SNumbers.norm_padFin_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:09:29.196097+00:00
-- url     : https://prove2.me/submissions/66dfd202-ca7f-4cca-8152-32481b0222ef

module
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_SNumbers_padFin_castLE
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
theorem _root_.solution (h : n ≤ m) (y : PiLp p (fun _ : Fin n => 𝕜)) :
    ‖padFin (p := p) (m := m) y‖ ≤ ‖y‖ := by
  rcases p.dichotomy with (rfl | hp)
  · rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_ciSup]
    rcases isEmpty_or_nonempty (Fin m) with _ | _
    · rw [Real.iSup_of_isEmpty]
      exact Real.iSup_nonneg fun j => norm_nonneg _
    · refine ciSup_le fun i => ?_
      by_cases hi : (i : ℕ) < n
      · simpa [padFin_apply, hi] using
          le_ciSup (Finite.bddAbove_range fun j => ‖y j‖) (⟨(i : ℕ), hi⟩ : Fin n)
      · simp only [padFin_apply, dif_neg hi, norm_zero]
        exact Real.iSup_nonneg fun j => norm_nonneg _
  · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
    rw [PiLp.norm_eq_sum hp0, PiLp.norm_eq_sum hp0]
    apply le_of_eq
    congr 1
    have hoff : ∑ i : Fin m, ‖(padFin (p := p) (m := m) y) i‖ ^ p.toReal
        = ∑ i ∈ Finset.univ.image (Fin.castLE h),
            ‖(padFin (p := p) (m := m) y) i‖ ^ p.toReal := by
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro i _ hi
      have hni : ¬ (i : ℕ) < n := fun hlt =>
        hi (Finset.mem_image.mpr ⟨⟨(i : ℕ), hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      rw [padFin_apply, dif_neg hni, norm_zero, Real.zero_rpow hp0.ne']
    rw [hoff, Finset.sum_image fun a _ b _ hab => Fin.castLE_injective h hab]
    exact Finset.sum_congr rfl fun j _ => by rw [padFin_castLE]
end SNumbers
