-- Prove2me | solution 1 for SumProduct.exists_place_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:50:46.282425+00:00
-- url     : https://prove2.me/submissions/3cc6741b-297e-4c54-8cde-a39682ff8129

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField NumberField.InfinitePlace
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {γ : 𝓞 K} (hγ : γ ≠ 0) :
    ∃ w : InfinitePlace K, 1 ≤ w (γ : K) := by
  classical
  by_contra h
  push Not at h
  have hnorm_ne : Algebra.norm ℤ γ ≠ 0 := Algebra.norm_ne_zero_iff.mpr hγ
  have hge : (1 : ℝ) ≤ ∏ w : InfinitePlace K, w (γ : K) ^ mult w := by
    rw [prod_eq_abs_norm, ← Algebra.coe_norm_int]
    have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ γ| := Int.one_le_abs hnorm_ne
    push_cast
    exact_mod_cast h1
  have hlt : (∏ w : InfinitePlace K, w (γ : K) ^ mult w) < 1 := by
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w₀)]
    have hfac_lt : w₀ (γ : K) ^ mult w₀ < 1 :=
      pow_lt_one₀ (apply_nonneg w₀ _) (h w₀) mult_ne_zero
    have hrest_le : (∏ w ∈ Finset.univ.erase w₀, w (γ : K) ^ mult w) ≤ 1 :=
      Finset.prod_le_one (fun w _ => by positivity)
        (fun w _ => pow_le_one₀ (apply_nonneg w _) (h w).le)
    calc w₀ (γ : K) ^ mult w₀ * ∏ w ∈ Finset.univ.erase w₀, w (γ : K) ^ mult w
        ≤ w₀ (γ : K) ^ mult w₀ * 1 := mul_le_mul_of_nonneg_left hrest_le (by positivity)
      _ = w₀ (γ : K) ^ mult w₀ := mul_one _
      _ < 1 := hfac_lt
  linarith
end SumProduct
