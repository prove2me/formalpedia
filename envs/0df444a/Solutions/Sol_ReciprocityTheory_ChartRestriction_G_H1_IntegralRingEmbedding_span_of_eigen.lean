-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding.span_of_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:27:10.818669+00:00
-- url     : https://prove2.me/submissions/8ae7b884-29ad-4b54-946b-2e9079032f3c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_NakayamaChar
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IntegralRingEmbedding
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_IntegralRingEmbedding_val_root_unity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_IntegralRingEmbedding_val_sub_roots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
open Module
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))
variable {W : Type} [AddCommGroup W] [Module F W] {n : ℕ} (b : Fin n → W)
namespace ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
theorem _root_.solution (UU Pos : W → Prop) (hb : LinearIndependent F b)
    (hUU : ∀ s, UU s ↔ ∃ c : Fin n → F, (∀ i, 0 ≤ v (c i)) ∧ s = ∑ i, c i • b i)
    (hPos : ∀ s, UU s → ∀ ζ : F, ∀ s', 0 < v ζ → UU s' → s = ζ • s' → Pos s)
    (hπ : ∃ π : F, 0 < v π)
    {ι Γ : Type} [Fintype ι] (hcard : Fintype.card ι = n) (sv : ι → W)
    (hsv : ∀ i, UU (sv i)) (hsvp : ∀ i, ¬ Pos (sv i))
    (T : Γ → W →ₗ[F] W) (hT : ∀ γ s, UU s → UU (T γ s))
    {N : ℕ} (hN : 1 ≤ N) (hvN : v (N : F) = 0) (χ : ι → Γ → F)
    (hχN : ∀ i γ, χ i γ ^ N = 1) (heig : ∀ i γ, T γ (sv i) = χ i γ • sv i)
    (hsep : ∀ i j, i ≠ j → ∃ γ, χ i γ ≠ χ j γ) :
    ∀ s, UU s → ∃ a : ι → F, (∀ i, 0 ≤ v (a i)) ∧ s = ∑ i, a i • sv i := by
  classical
  have hUU0 : UU 0 := (hUU 0).2 ⟨0, fun i => by simp, by simp⟩
  have hUUsub : ∀ s t, UU s → UU t → UU (s - t) := by
    intro s t hs ht
    obtain ⟨c, hc, rfl⟩ := (hUU s).1 hs
    obtain ⟨d, hd, rfl⟩ := (hUU _).1 ht
    refine (hUU _).2 ⟨c - d, fun i => ?_, ?_⟩
    · exact le_trans (le_min (hc i) (hd i)) (AddValuation.map_sub v (c i) (d i))
    · simp [sub_smul, Finset.sum_sub_distrib]
  have hUUsmul : ∀ r s, 0 ≤ v r → UU s → UU (r • s) := by
    intro r s hr hs
    obtain ⟨c, hc, rfl⟩ := (hUU s).1 hs
    refine (hUU _).2 ⟨fun i => r * c i, fun i => ?_, ?_⟩
    · show 0 ≤ v (r * c i)
      rw [AddValuation.map_mul]
      exact add_nonneg hr (hc i)
    · simp [Finset.smul_sum, mul_smul]
  have hsv0 : ∀ i, sv i ≠ 0 := by
    intro i h
    apply hsvp i
    exact hPos (sv i) (hsv i) 0 0 (by simp) hUU0 (by rw [h, zero_smul])
  have hχv : ∀ i γ, v (χ i γ) = 0 := fun i γ => val_root_unity v hN (hχN i γ)
  have hχd : ∀ i j γ, χ i γ ≠ χ j γ → v (χ i γ - χ j γ) = 0 :=
    fun i j γ h => val_sub_roots v hN hvN (hχN i γ) (hχN j γ) h

  have hred : ∀ (S : Finset ι) (a : ι → F) (j : ι) (γ : Γ), j ∈ S →
      T γ (∑ i ∈ S, a i • sv i) - χ j γ • ∑ i ∈ S, a i • sv i =
        ∑ i ∈ S.erase j, (a i * (χ i γ - χ j γ)) • sv i := by
    intro S a j γ hj
    rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    have hterm : ∀ i, T γ (a i • sv i) - χ j γ • (a i • sv i) = (a i * (χ i γ - χ j γ)) • sv i := by
      intro i
      rw [map_smul, heig, smul_smul, smul_smul, ← sub_smul]
      congr 1
      ring
    simp_rw [hterm]
    rw [← Finset.sum_erase_add _ _ hj, sub_self, mul_zero, zero_smul, add_zero]

  have indep : ∀ S : Finset ι, ∀ a : ι → F, ∑ i ∈ S, a i • sv i = 0 → ∀ k ∈ S, a k = 0 := by
    intro S
    induction S using Finset.strongInduction
    rename_i S ih
    intro a ha k hk
    by_cases hex : ∃ j ∈ S, j ≠ k
    · obtain ⟨j, hj, hjk⟩ := hex
      obtain ⟨γ, hγ⟩ := hsep k j (Ne.symm hjk)
      have hz : ∑ i ∈ S.erase j, (a i * (χ i γ - χ j γ)) • sv i = 0 := by
        rw [← hred S a j γ hj, ha, map_zero, smul_zero, sub_zero]
      have h1 : a k * (χ k γ - χ j γ) = 0 :=
        ih (S.erase j) (Finset.erase_ssubset hj) (fun i => a i * (χ i γ - χ j γ)) hz k
          (Finset.mem_erase.2 ⟨Ne.symm hjk, hk⟩)
      exact (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 hγ)
    · rw [Finset.sum_eq_single k (fun j hj hjk => absurd ⟨j, hj, hjk⟩ hex)
        (fun h => absurd hk h)] at ha
      exact (smul_eq_zero.1 ha).resolve_right (hsv0 k)

  have key : ∀ S : Finset ι, ∀ a : ι → F, UU (∑ i ∈ S, a i • sv i) → ∀ k ∈ S, 0 ≤ v (a k) := by
    intro S
    induction S using Finset.strongInduction
    rename_i S ih
    intro a ha k hk
    by_cases hex : ∃ j ∈ S, j ≠ k
    · obtain ⟨j, hj, hjk⟩ := hex
      obtain ⟨γ, hγ⟩ := hsep k j (Ne.symm hjk)
      have hmem : UU (∑ i ∈ S.erase j, (a i * (χ i γ - χ j γ)) • sv i) := by
        rw [← hred S a j γ hj]
        exact hUUsub _ _ (hT γ _ ha) (hUUsmul _ _ (le_of_eq (hχv j γ).symm) ha)
      have h1 : 0 ≤ v (a k * (χ k γ - χ j γ)) :=
        ih (S.erase j) (Finset.erase_ssubset hj) (fun i => a i * (χ i γ - χ j γ)) hmem k
          (Finset.mem_erase.2 ⟨Ne.symm hjk, hk⟩)
      rw [AddValuation.map_mul, hχd k j γ hγ, add_zero] at h1
      exact h1
    · rw [Finset.sum_eq_single k (fun j hj hjk => absurd ⟨j, hj, hjk⟩ hex)
        (fun h => absurd hk h)] at ha
      by_contra hneg
      have hneg' : v (a k) < 0 := not_le.1 hneg
      have hak : a k ≠ 0 := by
        intro h0
        rw [h0, AddValuation.map_zero] at hneg'
        exact absurd hneg' (not_lt.2 le_top)
      have hsum : v (a k) + v (a k)⁻¹ = 0 := by
        rw [← AddValuation.map_mul, mul_inv_cancel₀ hak, AddValuation.map_one]
      have hpos : 0 < v (a k)⁻¹ := by
        refine lt_of_le_of_ne (wt_inv_nonneg hsum hneg') ?_
        intro h0
        rw [← h0, add_zero] at hsum
        rw [hsum] at hneg'
        exact lt_irrefl _ hneg'
      exact hsvp k (hPos (sv k) (hsv k) (a k)⁻¹ (a k • sv k) hpos ha
        (by rw [smul_smul, inv_mul_cancel₀ hak, one_smul]))
  have hli : LinearIndependent F sv := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    exact indep Finset.univ g hg i (Finset.mem_univ i)
  have hmemb : ∀ s, UU s → s ∈ Submodule.span F (Set.range b) := by
    intro s hs
    obtain ⟨c, -, rfl⟩ := (hUU s).1 hs
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  haveI : FiniteDimensional F (Submodule.span F (Set.range b)) :=
    FiniteDimensional.span_of_finite F (Set.finite_range b)
  have hspan : Submodule.span F (Set.range sv) = Submodule.span F (Set.range b) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hmemb _ (hsv i)
    · rw [finrank_span_eq_card hli, finrank_span_eq_card hb, hcard, Fintype.card_fin]
  intro s hs
  have hs' : s ∈ Submodule.span F (Set.range sv) := by
    rw [hspan]
    exact hmemb s hs
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hs'
  refine ⟨a, fun i => key Finset.univ a ?_ i (Finset.mem_univ i), ha.symm⟩
  rw [ha]
  exact hs
end ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
