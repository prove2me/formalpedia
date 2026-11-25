-- Prove2me | solution 1 for Supermultiplicative.tendsto_lim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:29:05.890196+00:00
-- url     : https://prove2.me/submissions/d93c5b44-6c04-4f54-9d17-e23a7a7ad512

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_Fekete_Superadditive
public import Theorems.Thm_superadditive_neg_iff
public import Theorems.Thm_subadditive_neg_iff
public import Theorems.Thm_Superadditive_tendsto_lim
attribute [local simp] superadditive_neg_iff
attribute [local simp] subadditive_neg_iff
section
@[expose] public section
noncomputable section
open Filter Set
open scoped Topology
namespace Superadditive
variable {u : ℕ → ℝ} (h : Superadditive u)
end Superadditive
namespace Supermultiplicative
variable {u : ℕ → ℝ}
private theorem superadditive_log_ite (h : Supermultiplicative u)
    (hpos : ∀ n, n ≠ 0 → 0 < u n) :
    Superadditive fun n ↦ if n = 0 then 0 else Real.log (u n) := fun m n ↦ by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hmn : m + n ≠ 0 := by omega
  simp only [hm, hn, hmn, ↓reduceIte]
  rw [← Real.log_mul (hpos m hm).ne' (hpos n hn).ne']
  exact Real.log_le_log (mul_pos (hpos m hm) (hpos n hn)) (h m n)
private theorem ite_log_div (u : ℕ → ℝ) :
    (fun n : ℕ ↦ (if n = 0 then 0 else Real.log (u n)) / n) = fun n ↦ Real.log (u n) / n := by
  funext n
  split_ifs with hn <;> simp [hn]
private theorem rpow_inv_eq_exp (hpos : ∀ n, n ≠ 0 → 0 < u n) (n : ℕ) :
    u n ^ (n : ℝ)⁻¹ = Real.exp (Real.log (u n) / n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [Real.rpow_def_of_pos (hpos n hn), div_eq_mul_inv]
end Supermultiplicative
end
end
end

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
open Supermultiplicative
variable {u : ℕ → ℝ}
namespace Supermultiplicative
theorem _root_.solution (h : Supermultiplicative u) (hpos : ∀ n, n ≠ 0 → 0 < u n)
    (hbdd : BddAbove (range fun n ↦ u n ^ (n : ℝ)⁻¹)) :
    Tendsto (fun n ↦ u n ^ (n : ℝ)⁻¹) atTop (𝓝 (Supermultiplicative.lim u)) := by
  have hs := h.superadditive_log_ite hpos
  have hbdd' : BddAbove (range fun n ↦ Real.log (u n) / n) := by
    obtain ⟨b, hb⟩ := hbdd
    have hb0 : 0 < b := one_pos.trans_le (by simpa using hb ⟨0, rfl⟩)
    refine ⟨Real.log b, ?_⟩
    rintro _ ⟨n, rfl⟩
    have := hb ⟨n, rfl⟩
    simp only [rpow_inv_eq_exp hpos] at this
    exact (Real.le_log_iff_exp_le hb0).2 this
  have hlim := hs.tendsto_lim (by rwa [ite_log_div])
  rw [ite_log_div] at hlim
  have hexp := (Real.continuous_exp.tendsto _).comp hlim
  have hfun : (Real.exp ∘ fun n ↦ Real.log (u n) / n) = fun n ↦ u n ^ (n : ℝ)⁻¹ :=
    funext fun n ↦ (rpow_inv_eq_exp hpos n).symm
  rw [hfun] at hexp
  convert hexp using 2
  rw [Supermultiplicative.lim, Superadditive.lim, ite_log_div,
    Real.exp_monotone.map_csSup_of_continuousAt Real.continuous_exp.continuousAt
      ((nonempty_Ici).image _) (hbdd'.mono (image_subset_range _ _)), image_image]
  simp [rpow_inv_eq_exp hpos]
end Supermultiplicative
