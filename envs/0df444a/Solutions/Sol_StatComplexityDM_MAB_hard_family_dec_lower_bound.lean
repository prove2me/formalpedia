-- Prove2me | solution 1 for StatComplexityDM.MAB.hard_family_dec_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:26:28.514553+00:00
-- url     : https://prove2.me/submissions/e86a5485-1274-4851-b1a7-2051a68d8d2d

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_DEC
import Definitions.Def_StatComplexityDM_LowerBound_Core
import Definitions.Def_StatComplexityDM_MAB_HardFamily

open FoundationsRL.GeneralDM

open StatComplexityDM.MAB in
theorem solution {S Y : Type*} [Fintype S] [Fintype Y] [Nonempty S]
    (rew : Y → ℝ) (piStar : (S → Y → ℝ) → S)
    (𝓜 : Set (S → Y → ℝ)) (mbar : S → Y → ℝ) {N : ℕ}
    (fam : Fin N → S → Y → ℝ) (α β δ : ℝ) (hβ : 0 ≤ β)
    (hfam : IsHardFamily 𝓜 rew piStar mbar fam α β δ)
    (γ : ℝ) (hγ : 0 < γ) :
    α / 2 - γ * (β / N + δ) ≤ decGf (Set.range fam) rew piStar γ mbar := by
  obtain ⟨-, hargmax, -, hfamM, hN, ⟨u, hu1, hu2, hu3⟩, ⟨v, hv1, hv2, hv3⟩⟩ := hfam
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set c := α * N / 2 - γ * (β + N * δ) with hc
  have hper : ∀ π, c ≤ ∑ i, ((fM rew (fam i) (piStar (fam i)) - fM rew (fam i) π) -
      γ * hellingerSq (fam i π) (mbar π)) := by
    intro π
    have hg : α * N / 2 ≤ ∑ i, (fM rew (fam i) (piStar (fam i)) - fM rew (fam i) π) := by
      rcases le_or_gt 0 α with ha | ha
      · have h1 : ∑ i : Fin N, α * (1 - u i π) = α * (N - ∑ i, u i π) := by
          rw [← Finset.mul_sum, Finset.sum_sub_distrib]
          simp
        have h2 : ∑ i : Fin N, α * (1 - u i π) ≤
            ∑ i, (fM rew (fam i) (piStar (fam i)) - fM rew (fam i) π) :=
          Finset.sum_le_sum (fun i _ => hu3 i π)
        have h3 := hu2 π
        nlinarith
      · have : 0 ≤ ∑ i, (fM rew (fam i) (piStar (fam i)) - fM rew (fam i) π) :=
          Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hargmax _ (hfamM i) π))
        nlinarith
    have hh : ∑ i, hellingerSq (fam i π) (mbar π) ≤ β + N * δ := by
      have h1 : ∑ i, hellingerSq (fam i π) (mbar π) ≤ ∑ i : Fin N, (β * v i π + δ) :=
        Finset.sum_le_sum (fun i _ => hv3 i π)
      have h2 : ∑ i : Fin N, (β * v i π + δ) = β * ∑ i, v i π + N * δ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
      have h3 := hv2 π
      nlinarith
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    nlinarith
  have hcB : c = N * (α / 2 - γ * (β / N + δ)) := by
    rw [hc]; field_simp <;> ring
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  unfold decGf
  apply le_csInf
  · refine ⟨_, ⟨fun _ => 1 / (Fintype.card S : ℝ), ⟨fun _ => by positivity, ?_⟩, rfl⟩⟩
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (0:ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
    field_simp
  · rintro _ ⟨p, ⟨hp0, hp1⟩, rfl⟩
    have hsum : ∑ i : Fin N, (∑ π, p π * (fM rew (fam i) (piStar (fam i)) - fM rew (fam i) π
        - γ * hellingerSq (fam i π) (mbar π))) =
        ∑ π, p π * ∑ i, ((fM rew (fam i) (piStar (fam i)) - fM rew (fam i) π) -
          γ * hellingerSq (fam i π) (mbar π)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun π _ => ?_)
      rw [Finset.mul_sum]
    have hlow : c ≤ ∑ π, p π * ∑ i, ((fM rew (fam i) (piStar (fam i)) - fM rew (fam i) π) -
          γ * hellingerSq (fam i π) (mbar π)) := by
      calc c = ∑ π, p π * c := by rw [← Finset.sum_mul, hp1, one_mul]
        _ ≤ _ := Finset.sum_le_sum (fun π _ => mul_le_mul_of_nonneg_left (hper π) (hp0 π))
    obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le hne
      (f := fun _ => α / 2 - γ * (β / N + δ))
      (g := fun i => ∑ π, p π * (fM rew (fam i) (piStar (fam i)) - fM rew (fam i) π
        - γ * hellingerSq (fam i π) (mbar π))) (by
        rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← hcB]
        exact hlow)
    refine le_trans hi ?_
    apply le_csSup ((Set.finite_range fam).image _).bddAbove
    exact ⟨fam i, ⟨i, rfl⟩, rfl⟩
