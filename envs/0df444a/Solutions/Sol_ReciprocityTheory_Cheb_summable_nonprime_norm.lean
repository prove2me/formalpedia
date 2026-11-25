-- Prove2me | solution 1 for ReciprocityTheory.Cheb.summable_nonprime_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:36:25.11936+00:00
-- url     : https://prove2.me/submissions/4f8b51b7-8a23-4994-86dd-da23a3fb0c53

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_CycTail
import Theorems.Thm_ReciprocityTheory_Cheb_primeBelow_prime
import Theorems.Thm_ReciprocityTheory_Cheb_card_filter_primeBelow_le
import Theorems.Thm_ReciprocityTheory_Cheb_nonprime_term_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution :
    Summable (fun q : Prm E => if (Nrm q).Prime then (0 : ℝ) else ((Nrm q : ℕ) : ℝ)⁻¹) := by
  classical
  let G : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2
  have hG : Summable G := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hG0 : ∀ n, 0 ≤ G n := fun n => by positivity
  refine summable_of_sum_le (c := Module.finrank ℚ E * ∑' n, G n) (fun q => by
    dsimp only; split_ifs <;> positivity) (fun u => ?_)
  calc ∑ x ∈ u, (if (Nrm x).Prime then (0 : ℝ) else ((Nrm x : ℕ) : ℝ)⁻¹)
        ≤ ∑ x ∈ u, G (primeBelow x) := Finset.sum_le_sum fun x _ => nonprime_term_le x
    _ = ∑ b ∈ u.image (fun x => primeBelow x),
          (u.filter fun x => primeBelow x = b).card • G b := Finset.sum_comp _ _
    _ ≤ ∑ b ∈ u.image (fun x => primeBelow x), (Module.finrank ℚ E : ℝ) * G b := by
        refine Finset.sum_le_sum fun b hb => ?_
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hb
        rw [nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (hG0 _)
        exact_mod_cast card_filter_primeBelow_le u _ (primeBelow_prime x)
    _ = (Module.finrank ℚ E : ℝ) * ∑ b ∈ u.image (fun x => primeBelow x), G b := by
        rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ E : ℝ) * ∑' n, G n :=
        mul_le_mul_of_nonneg_left (hG.sum_le_tsum _ fun n _ => hG0 n) (by positivity)
end ReciprocityTheory.Cheb
