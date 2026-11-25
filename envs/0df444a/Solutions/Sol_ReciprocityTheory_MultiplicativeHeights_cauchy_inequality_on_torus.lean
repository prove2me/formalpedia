-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.cauchy_inequality_on_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:27:41.656186+00:00
-- url     : https://prove2.me/submissions/2f431c3d-804c-4375-ba2b-818a17c47a2e

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsTorusPointOneLeNormSum
import Definitions.Def_ReciprocityTheory_SemistableReduction_CauchyInequalityOnTorus
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_exists_torus_point_one_le_norm_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution : CauchyTorusStatement := by
  intro K _ _ _ K₀ hK₀ n c hc hτ χ
  by_contra hχ
  push_neg at hχ
  have hev : ∀ᶠ ψ in Filter.cofinite, ‖c ψ‖ < 1 / 2 := hc.eventually (gt_mem_nhds (by norm_num))
  have hFfin : {ψ | ¬ ‖c ψ‖ < 1 / 2}.Finite := Filter.eventually_cofinite.1 hev
  set F := hFfin.toFinset with hFdef
  have hχF : χ ∈ F := by
    rw [Set.Finite.mem_toFinset]
    show ¬ ‖c χ‖ < 1 / 2
    linarith
  obtain ⟨χm, hχmF, hmax⟩ := F.exists_max_image (fun ψ => ‖c ψ‖) ⟨χ, hχF⟩
  have hgt : 1 < ‖c χm‖ := lt_of_lt_of_le hχ (hmax χ hχF)
  have hglob : ∀ ψ, ‖c ψ‖ ≤ ‖c χm‖ := by
    intro ψ
    by_cases hψ : ψ ∈ F
    · exact hmax ψ hψ
    · have h2 : ‖c ψ‖ < 1 / 2 := by
        rw [Set.Finite.mem_toFinset] at hψ
        simpa using hψ
      linarith
  set lam := c χm with hlam
  have hlam0 : lam ≠ 0 := by
    intro h
    rw [h, norm_zero] at hgt
    linarith
  set a : (Fin n → ℤ) → K := fun ψ => c ψ / lam with hadef
  have ha : ∀ ψ, ‖a ψ‖ ≤ 1 := by
    intro ψ
    simp only [hadef, norm_div]
    exact (div_le_one (norm_pos_iff.2 hlam0)).2 (hglob ψ)
  have ha0 : ‖a χm‖ = 1 := by
    simp only [hadef, norm_div]
    exact div_self (norm_ne_zero_iff.2 hlam0)
  obtain ⟨τ, hτu, hτ1⟩ := exists_torus_point_one_le_norm_sum K₀ hK₀ F a ha χm hχmF ha0
  have hprodnorm : ∀ ψ : Fin n → ℤ, ‖∏ i, τ i ^ ψ i‖ = 1 := by
    intro ψ
    rw [norm_prod]
    exact Finset.prod_eq_one fun i _ => by rw [norm_zpow, (hτu i).2, one_zpow]
  have hSF : ∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i = lam * ∑ ψ ∈ F, a ψ * ∏ i, τ i ^ ψ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    simp only [hadef]
    field_simp
  have hSFn : ‖lam‖ ≤ ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖ := by
    rw [hSF, norm_mul]
    calc ‖lam‖ = ‖lam‖ * 1 := (mul_one _).symm
      _ ≤ ‖lam‖ * ‖∑ ψ ∈ F, a ψ * ∏ i, τ i ^ ψ i‖ := mul_le_mul_of_nonneg_left hτ1 (norm_nonneg _)
  have hsum : Summable (fun ψ => c ψ * ∏ i, τ i ^ ψ i) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [norm_mul, hprodnorm] using hc
  have hsplit := hsum.sum_add_tsum_compl (s := F)
  have htail : ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖ ≤ 1 / 2 := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by norm_num) fun ψ => ?_
    rw [norm_mul, hprodnorm, mul_one]
    have hψ : (ψ : Fin n → ℤ) ∉ F := fun h => ψ.2 (Finset.mem_coe.2 h)
    rw [Set.Finite.mem_toFinset] at hψ
    simp only [Set.mem_setOf_eq, not_not] at hψ
    exact le_of_lt hψ
  have hne : ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖ ≠
      ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖ := by
    intro h
    linarith
  have htot := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [hsplit] at htot
  have h1 := hτ τ hτu
  unfold torusSum at h1
  rw [htot] at h1
  have h3 := le_max_left ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖
    ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖
  linarith
end ReciprocityTheory.MultiplicativeHeights
