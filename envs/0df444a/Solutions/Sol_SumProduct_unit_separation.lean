-- Prove2me | solution 1 for SumProduct.unit_separation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:22:13.838038+00:00
-- url     : https://prove2.me/submissions/befe364a-7670-4666-9dd0-6da42e57f5c0

import Mathlib
import Definitions.Def_SumProduct_UnitSeparation

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open Real NumberField NumberField.InfinitePlace
namespace SumProduct
theorem _root_.solution (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (u : (𝓞 K)ˣ)
    (h : ∀ w : InfinitePlace K,
      goldenRatio⁻¹ < w ((u : 𝓞 K) : K) ∧ w ((u : 𝓞 K) : K) < goldenRatio) :
    u = 1 ∨ u = -1 := by
  classical
  -- Real-analysis core: `φ⁻¹ < t < φ ⟹ t² + t⁻² - 2 < 1` (equivalently `(t - t⁻¹)² < 1`).
  have hreal : ∀ t : ℝ, goldenRatio⁻¹ < t → t < goldenRatio → t ^ 2 + t⁻¹ ^ 2 - 2 < 1 := by
    intro t h1 h2
    have hφ0 : (0 : ℝ) < goldenRatio := goldenRatio_pos
    have ht0 : 0 < t := lt_trans (inv_pos.mpr hφ0) h1
    set s := t⁻¹ with hs
    have hts : t * s = 1 := mul_inv_cancel₀ ht0.ne'
    have hs0 : 0 < s := inv_pos.mpr ht0
    have hpp1 : goldenRatio * goldenRatio⁻¹ = 1 := mul_inv_cancel₀ hφ0.ne'
    have httm : t ^ 2 - t - 1 < 0 := by
      have hψ : goldenConj < t := lt_trans goldenConj_neg ht0
      have := mul_neg_of_neg_of_pos (sub_neg.mpr h2) (sub_pos.mpr hψ)
      nlinarith [this, goldenRatio_add_goldenConj, goldenRatio_mul_goldenConj]
    have hub : t - s < 1 := by nlinarith [httm, hts, ht0]
    have hφt1 : 1 < goldenRatio * t := by
      have := mul_lt_mul_of_pos_left h1 hφ0
      rwa [hpp1] at this
    have hsltφ : s < goldenRatio := by nlinarith [hφt1, hts, ht0, hs0]
    have httm2 : s ^ 2 - s - 1 < 0 := by
      have hψ : goldenConj < s := lt_trans goldenConj_neg hs0
      have := mul_neg_of_neg_of_pos (sub_neg.mpr hsltφ) (sub_pos.mpr hψ)
      nlinarith [this, goldenRatio_add_goldenConj, goldenRatio_mul_goldenConj]
    have hlb : s - t < 1 := by nlinarith [httm2, hts, hs0]
    nlinarith [hub, hlb, hts]
  -- `α = u² + u⁻² - 2 ∈ 𝒪_K`.
  set a : 𝓞 K := (u : 𝓞 K) ^ 2 + ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ 2 - 2 with ha
  -- Step 1: `α = 0`.
  have hzero : a = 0 := by
    by_contra hne
    -- At each place, `w α < 1`.
    have hlt : ∀ w : InfinitePlace K, w (a : K) < 1 := by
      intro w
      have hw : w.IsReal := IsTotallyReal.isReal w
      set τ : 𝓞 K →+* ℝ := (embedding_of_isReal hw).comp (algebraMap (𝓞 K) K) with hτ
      have hwτ : ∀ x : 𝓞 K, w (x : K) = |τ x| := by
        intro x
        have hcomp : τ x = embedding_of_isReal hw (x : K) := rfl
        rw [hcomp, ← norm_embedding_of_isReal hw (x : K), Real.norm_eq_abs]
      have hu0 : τ (u : 𝓞 K) ≠ 0 := by
        have hpos : (0 : ℝ) < |τ (u : 𝓞 K)| := by
          rw [← hwτ (u : 𝓞 K)]; exact lt_trans (inv_pos.mpr goldenRatio_pos) (h w).1
        exact abs_pos.mp hpos
      have hτinv : τ ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = (τ (u : 𝓞 K))⁻¹ := by
        have h1 : τ (u : 𝓞 K) * τ ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        field_simp
        linear_combination h1
      have hexp : τ a = (τ (u : 𝓞 K)) ^ 2 + (τ (u : 𝓞 K))⁻¹ ^ 2 - 2 := by
        rw [ha]; simp only [map_sub, map_add, map_pow, map_ofNat, hτinv]
      have hnn : 0 ≤ τ a := by
        rw [hexp]; nlinarith [sq_nonneg (τ (u : 𝓞 K) - (τ (u : 𝓞 K))⁻¹),
          mul_inv_cancel₀ hu0]
      rw [hwτ a, abs_of_nonneg hnn, hexp]
      have e1 : (τ (u : 𝓞 K)) ^ 2 = |τ (u : 𝓞 K)| ^ 2 := (sq_abs _).symm
      have e2 : (τ (u : 𝓞 K))⁻¹ ^ 2 = |τ (u : 𝓞 K)|⁻¹ ^ 2 := by
        rw [← sq_abs ((τ (u : 𝓞 K))⁻¹), abs_inv]
      rw [e1, e2]
      have hb := h w
      rw [hwτ (u : 𝓞 K)] at hb
      exact hreal _ hb.1 hb.2
    -- The product of the `w α` is `|N(α)|`, both `< 1` and `≥ 1`: contradiction.
    have hnorm_ne : Algebra.norm ℤ a ≠ 0 := (Algebra.norm_ne_zero_iff).mpr hne
    have hge : (1 : ℝ) ≤ ∏ w : InfinitePlace K, w (a : K) ^ mult w := by
      rw [prod_eq_abs_norm, ← Algebra.coe_norm_int]
      have : (1 : ℤ) ≤ |Algebra.norm ℤ a| := Int.one_le_abs hnorm_ne
      push_cast
      exact_mod_cast this
    have hlt_prod : (∏ w : InfinitePlace K, w (a : K) ^ mult w) < 1 := by
      obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w₀)]
      have hfac_lt : w₀ (a : K) ^ mult w₀ < 1 :=
        pow_lt_one₀ (apply_nonneg w₀ _) (hlt w₀) mult_ne_zero
      have hrest_le : (∏ w ∈ Finset.univ.erase w₀, w (a : K) ^ mult w) ≤ 1 :=
        Finset.prod_le_one (fun w _ => by positivity)
          (fun w _ => pow_le_one₀ (apply_nonneg w _) (hlt w).le)
      calc w₀ (a : K) ^ mult w₀ * ∏ w ∈ Finset.univ.erase w₀, w (a : K) ^ mult w
          ≤ w₀ (a : K) ^ mult w₀ * 1 :=
            mul_le_mul_of_nonneg_left hrest_le (by positivity)
        _ = w₀ (a : K) ^ mult w₀ := mul_one _
        _ < 1 := hfac_lt
    linarith
  -- Step 2: `α = 0 ⟹ u = u⁻¹ ⟹ u = ±1`.
  have hxy : (u : 𝓞 K) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 1 := Units.mul_inv u
  have hsq : ((u : 𝓞 K) - ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) ^ 2 = a := by
    rw [ha, sub_sq]; rw [show (2 : 𝓞 K) * (u : 𝓞 K) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)
      = 2 * ((u : 𝓞 K) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) by ring, hxy]; ring
  have huv0 : (u : 𝓞 K) - ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 0 := by
    have : ((u : 𝓞 K) - ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) ^ 2 = 0 := by rw [hsq]; exact hzero
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have heq : (u : 𝓞 K) = ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := sub_eq_zero.mp huv0
  have husq : (u : 𝓞 K) * (u : 𝓞 K) = 1 := by
    nth_rewrite 2 [heq]; exact hxy
  rcases mul_self_eq_one_iff.mp husq with h1 | h1
  · exact Or.inl (Units.ext h1)
  · exact Or.inr (Units.ext (by rw [h1]; rfl))
end SumProduct
