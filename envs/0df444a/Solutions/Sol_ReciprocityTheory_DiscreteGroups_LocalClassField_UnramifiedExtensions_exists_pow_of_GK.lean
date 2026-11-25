-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.exists_pow_of_GK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:31:28.233438+00:00
-- url     : https://prove2.me/submissions/0e1a1e1a-cd40-45ee-aece-6ee183c39884

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemOfPowQKSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_sigBar_red
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_sigBar_of_mem
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_pow_pow_succ_sub
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_resK_of_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_eq_one_of_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sub_eq_one_of_pow_eq_one
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_not_dvd_qK_pow_sub_one
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_one_lt_qK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_qK_eq_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_red_eq_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_red_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField Polynomial
variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (σ : GK p K)
    {ζ : PadicAlgCl p} (hζ : ζ ^ (qK p K ^ n - 1) = 1) : ∃ i < n, σ ζ = ζ ^ (qK p K ^ i) := by
  obtain ⟨f, hf, hqf⟩ := qK_eq_pow K hK
  have hq := one_lt_qK K hK
  set q := qK p K with hqdef
  have hnd : ¬ p ∣ q ^ n - 1 := not_dvd_qK_pow_sub_one K hK hn
  have hm0 : q ^ n - 1 ≠ 0 := by rintro h; exact hnd (h ▸ dvd_zero p)
  have h1 := norm_eq_one_of_pow hm0 hζ
  set c := red ζ with hc
  have hcn : c ^ (q ^ n) = c := by
    rw [hc, ← red_pow h1.le, pow_pow_succ_sub (by omega) hζ]
  have : ExpChar (kbar p) p := ExpChar.prime Fact.out
  let φ : kbar p →+* kbar p := iterateFrobenius (kbar p) p f
  have hφ : ∀ x, φ x = x ^ q := fun x => by rw [hqf]; rfl
  let g : ℕ → (kbar p)[X] := fun i => X - C (c ^ (q ^ i))
  set h : (kbar p)[X] := ∏ i ∈ Finset.range n, g i with hh
  have hg : ∀ i, (g i).map φ = g (i + 1) := by
    intro i
    simp only [g, Polynomial.map_sub, map_X, map_C, hφ]
    rw [← pow_mul, ← pow_succ]
  have hmap : h.map φ = h := by
    rw [hh, Polynomial.map_prod]
    simp only [hg]
    have e1 := Finset.prod_range_succ g n
    have e2 := Finset.prod_range_succ' g n
    have e3 : g n = g 0 := by simp only [g, hcn, pow_zero, pow_one]
    have e4 : g 0 ≠ 0 := X_sub_C_ne_zero _
    rw [e1, e3] at e2
    exact (mul_right_cancel₀ e4 e2).symm
  have hcoef : ∀ k, h.coeff k ∈ resK p K := by
    intro k
    apply mem_resK_of_pow K hK
    rw [← hφ, ← coeff_map, hmap]
  have hmapσ : h.map (sigBar σ) = h := by
    ext k
    rw [coeff_map, sigBar_of_mem σ (hcoef k)]
  have h0 : h.eval c = 0 := by
    rw [hh, eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_range.2 hn)
    simp [g]
  have h2 : h.eval (sigBar σ c) = 0 := by
    conv_lhs => rw [← hmapσ]
    rw [eval_map, eval₂_at_apply, h0, map_zero]
  rw [hh, eval_prod, Finset.prod_eq_zero_iff] at h2
  obtain ⟨i, hi, h3⟩ := h2
  refine ⟨i, Finset.mem_range.1 hi, ?_⟩
  simp only [g, eval_sub, eval_X, eval_C, sub_eq_zero] at h3
  rw [hc, sigBar_red σ h1.le, ← red_pow h1.le] at h3
  by_contra hne
  have hσζ : (σ ζ) ^ (q ^ n - 1) = 1 := by rw [← map_pow, hζ, map_one]
  have hζi : (ζ ^ (q ^ i)) ^ (q ^ n - 1) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have h4 := norm_sub_eq_one_of_pow_eq_one hnd hσζ hζi hne
  have h5 := (red_eq_iff (norm_eq_one_of_pow hm0 hσζ).le (norm_eq_one_of_pow hm0 hζi).le).1 h3
  exact absurd h4 (ne_of_lt h5)
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
