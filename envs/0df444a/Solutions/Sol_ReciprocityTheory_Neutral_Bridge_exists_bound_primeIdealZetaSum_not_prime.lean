-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.exists_bound_primeIdealZetaSum_not_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:31:53.438137+00:00
-- url     : https://prove2.me/submissions/cad4837a-c6e6-4179-b30c-580e66aa491e

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_ExistsPrimeAbsNormOfHasDirichletDensity
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_ratPrimeBelow_prime
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_card_fiber_ratPrimeBelow_le
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_rpow_neg_le_inv_ratPrimeBelow_sq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.Neutral.Bridge
open NumberField IsDedekindDomain Filter Topology
variable {K : Type*} [Field K] [NumberField K]
private theorem sum_absNorm_rpow_neg_le_of_not_prime {ι : Type*} (g : ι → HeightOneSpectrum (𝓞 K))
    (hg : Function.Injective g) (U : Finset ι)
    (hU : ∀ x ∈ U, ¬ (Ideal.absNorm (g x).asIdeal).Prime) {s : ℝ} (hs : 1 < s) :
    ∑ x ∈ U, (Ideal.absNorm (g x).asIdeal : ℝ) ^ (-s) ≤
      (Module.finrank ℚ K : ℝ) * ∑' m : ℕ, 1 / (m : ℝ) ^ 2 := by
  have hsum : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.2 (by norm_num)
  calc ∑ x ∈ U, (Ideal.absNorm (g x).asIdeal : ℝ) ^ (-s)
      ≤ ∑ x ∈ U, 1 / (ratPrimeBelow (g x) : ℝ) ^ 2 :=
        Finset.sum_le_sum fun x hx => rpow_neg_le_inv_ratPrimeBelow_sq _ (hU x hx) hs
    _ = ∑ m ∈ U.image (fun x => ratPrimeBelow (g x)),
          ∑ x ∈ U.filter (fun x => ratPrimeBelow (g x) = m), 1 / (ratPrimeBelow (g x) : ℝ) ^ 2 :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem _ hx) _).symm
    _ = ∑ m ∈ U.image (fun x => ratPrimeBelow (g x)),
          ((U.filter (fun x => ratPrimeBelow (g x) = m)).card : ℝ) * (1 / (m : ℝ) ^ 2) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_congr rfl (g := fun _ => 1 / (m : ℝ) ^ 2)
          (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ m ∈ U.image (fun x => ratPrimeBelow (g x)), (Module.finrank ℚ K : ℝ) * (1 / (m : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun m hm => ?_
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hm
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast card_fiber_ratPrimeBelow_le g hg U _ (ratPrimeBelow_prime _)
    _ = (Module.finrank ℚ K : ℝ) * ∑ m ∈ U.image (fun x => ratPrimeBelow (g x)), 1 / (m : ℝ) ^ 2 :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (Module.finrank ℚ K : ℝ) * ∑' m : ℕ, 1 / (m : ℝ) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        exact hsum.sum_le_tsum _ (fun m _ => by positivity)
end ReciprocityTheory.Neutral.Bridge
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge
open NumberField IsDedekindDomain Filter Topology
variable {K : Type*} [Field K] [NumberField K]
namespace ReciprocityTheory.Neutral.Bridge
theorem _root_.solution :
    ∃ C : ℝ, ∀ s : ℝ, 1 < s →
      NumberField.Set.primeIdealZetaSum {𝔭 : HeightOneSpectrum (𝓞 K) | ¬ (Ideal.absNorm 𝔭.asIdeal).Prime} s ≤ C := by
  refine ⟨(Module.finrank ℚ K : ℝ) * ∑' m : ℕ, 1 / (m : ℝ) ^ 2, fun s hs => ?_⟩
  unfold NumberField.Set.primeIdealZetaSum
  refine tsum_le_of_sum_le' (mul_nonneg (Nat.cast_nonneg _) (tsum_nonneg fun m => by positivity))
    fun U => ?_
  exact sum_absNorm_rpow_neg_le_of_not_prime Subtype.val Subtype.val_injective U (fun x _ => x.2) hs
end ReciprocityTheory.Neutral.Bridge
