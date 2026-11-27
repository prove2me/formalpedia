-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.exists_prime_absNorm_of_hasDirichletDensity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:32:00.942814+00:00
-- url     : https://prove2.me/submissions/f1598863-a97b-4688-87bc-07b8ba18a5c3

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_ExistsPrimeAbsNormOfHasDirichletDensity
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_ratPrimeBelow_prime
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_card_fiber_ratPrimeBelow_le
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_rpow_neg_le_inv_ratPrimeBelow_sq
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_DedekindZetaReal_two_le_absNorm
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_tendsto_primeIdealZetaSum_univ

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
theorem _root_.solution {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (h : NumberField.Set.HasDirichletDensity S δ) (hδ : 0 < δ) {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite) :
    ∃ 𝔭 ∈ S, 𝔭 ∉ T ∧ (Ideal.absNorm 𝔭.asIdeal).Prime := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨B, hB0, hbound⟩ : ∃ B : ℝ, 0 ≤ B ∧
      ∀ s : ℝ, 1 < s → NumberField.Set.primeIdealZetaSum S s ≤ B := by
    refine ⟨(hT.toFinset.card : ℝ) + (Module.finrank ℚ K : ℝ) * ∑' m : ℕ, 1 / (m : ℝ) ^ 2,
      add_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
        (tsum_nonneg fun m => by positivity)), fun s hs => ?_⟩
    unfold NumberField.Set.primeIdealZetaSum
    refine tsum_le_of_sum_le' (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
        (tsum_nonneg fun m => by positivity))) fun U => ?_
    rw [← Finset.sum_filter_add_sum_filter_not U
      (fun x : S => (x : HeightOneSpectrum (𝓞 K)) ∈ T)]
    refine add_le_add ?_ ?_
    · calc ∑ x ∈ U.filter (fun x : S => (x : HeightOneSpectrum (𝓞 K)) ∈ T),
            (Ideal.absNorm (x : HeightOneSpectrum (𝓞 K)).asIdeal : ℝ) ^ (-s)
          ≤ ∑ x ∈ U.filter (fun x : S => (x : HeightOneSpectrum (𝓞 K)) ∈ T), (1 : ℝ) := by
            refine Finset.sum_le_sum fun x _ => Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
            have := ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.two_le_absNorm (K := K) (x : HeightOneSpectrum (𝓞 K))
            linarith
        _ = ((U.filter (fun x : S => (x : HeightOneSpectrum (𝓞 K)) ∈ T)).card : ℝ) := by simp
        _ ≤ (hT.toFinset.card : ℝ) := by
            refine Nat.cast_le.2 (Finset.card_le_card_of_injOn Subtype.val ?_
              Subtype.val_injective.injOn)
            intro x hx
            have hx' := (Finset.mem_filter.1 hx).2
            exact (Set.Finite.mem_toFinset hT).2 hx'
    · refine sum_absNorm_rpow_neg_le_of_not_prime (ι := S) Subtype.val Subtype.val_injective _ ?_ hs
      intro x hx
      exact hcon x.1 x.2 (Finset.mem_filter.1 hx).2
  have h' : Tendsto (fun s => NumberField.Set.primeIdealZetaSum S s /
      NumberField.Set.primeIdealZetaSum Set.univ s) (𝓝[>] 1) (𝓝 δ) := h
  have hU := tendsto_primeIdealZetaSum_univ (K := K)
  have h1 : ∀ᶠ s in 𝓝[>] (1 : ℝ), δ / 2 < NumberField.Set.primeIdealZetaSum S s /
      NumberField.Set.primeIdealZetaSum Set.univ s :=
    h'.eventually (lt_mem_nhds (show δ / 2 < δ by linarith))
  have h2 : ∀ᶠ s in 𝓝[>] (1 : ℝ), 2 * (B + 1) / δ <
      NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s :=
    hU.eventually (eventually_gt_atTop (2 * (B + 1) / δ))
  have h3 : ∀ᶠ s in 𝓝[>] (1 : ℝ), s ∈ Set.Ioi (1 : ℝ) := self_mem_nhdsWithin
  obtain ⟨s, hs1, hs2, hs3⟩ := (h1.and (h2.and h3)).exists
  have hc : 0 < 2 * (B + 1) / δ := div_pos (by linarith) hδ
  have hpos : 0 < NumberField.Set.primeIdealZetaSum
      (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s := lt_trans hc hs2
  have hS := hbound s hs3
  have h4 : δ / 2 * NumberField.Set.primeIdealZetaSum
      (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s < NumberField.Set.primeIdealZetaSum S s := by
    exact (lt_div_iff₀ hpos).1 hs1
  have h5 : δ / 2 * (2 * (B + 1) / δ) < δ / 2 * NumberField.Set.primeIdealZetaSum
      (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s :=
    mul_lt_mul_of_pos_left hs2 (by linarith)
  have h6 : δ / 2 * (2 * (B + 1) / δ) = B + 1 := by
    have hδ' : δ ≠ 0 := hδ.ne'
    field_simp
    try ring
  rw [h6] at h5
  linarith
end ReciprocityTheory.Neutral.Bridge
