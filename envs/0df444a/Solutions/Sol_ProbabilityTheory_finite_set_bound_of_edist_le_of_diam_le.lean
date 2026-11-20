-- Prove2me | solution 1 for ProbabilityTheory.finite_set_bound_of_edist_le_of_diam_le
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T14:47:25.592658+00:00
-- url     : https://prove2.me/submissions/cf28e4a7-fb94-4fb8-b54f-bdf0c001b8ac

import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F002
import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F003

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Stochastic processes satisfying the Kolmogorov condition

-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal Finset

section Aux

end Aux

namespace ProbabilityTheory

variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E]
  {p q : ℝ} {M : ℝ≥0} {P : Measure Ω} {X : T → Ω → E}

section Measurability

variable [MeasurableSpace E] [BorelSpace E]

end Measurability

section FirstTerm

variable {J : Set T}

end FirstTerm

section SecondTerm

variable {J : Set T} {C : ℕ → Finset T} {ε : ℕ → ℝ≥0} {j k m : ℕ}

end SecondTerm

section Together

variable {M : ℝ≥0} {d p q : ℝ} {J : Set T} {c : ℝ≥0∞} {δ : ℝ≥0}


open Filter Topology

lemma lintegral_sup_cover_eq_of_lt_iInf_dist {C : Set T} {ε : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M)
    (hJ : J.Finite) (hC : IsCover ε J C) (hC_subset : C ⊆ J)
    (hε_lt : ε < ⨅ (s : J) (t : J) (_h : 0 < edist s t), edist s t) :
    ∫⁻ ω, ⨆ (s : C) (t : { t : C // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P
      = ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P := by
  have h_le_iff {s t : T} (hs : s ∈ J) (ht : t ∈ J) : edist s t ≤ ε ↔ edist s t = 0 := by
    refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
    by_contra h_ne_zero
    have h_pos : 0 < edist s t := by positivity
    refine lt_irrefl (ε : ℝ≥0∞) (hε_lt.trans_le ?_)
    refine (iInf_le _ ⟨s, hs⟩).trans <| (iInf_le _ ⟨t, ht⟩).trans ?_
    simp [h_pos, h]
  have hC_zero : IsCover 0 J C := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := hC hs
    simp only [ENNReal.coe_zero, nonpos_iff_eq_zero, Set.mem_ofPred_eq] at hst ⊢
    rw [h_le_iff hs (hC_subset ht)] at hst
    exact ⟨t, ht, hst⟩
  apply le_antisymm
  · gcongr with ω
    refine iSup_le fun s ↦ iSup_le fun t ↦ ?_
    exact le_iSup_of_le ⟨s.1, hC_subset s.2⟩ <| le_iSup_of_le ⟨⟨t.1, hC_subset t.1.2⟩, t.2⟩ le_rfl
  · choose f' hf'C hf'_edist using hC_zero
    simp only [ENNReal.coe_zero, nonpos_iff_eq_zero, Set.mem_ofPred_eq] at hf'_edist
    let f : J → C := fun s ↦ ⟨f' s.2, hf'C s.2⟩
    have hf_edist (s : J) : edist s.1 (f s).1 = 0 := hf'_edist s.2
    have hfX_edist (s : J) : ∀ᵐ ω ∂P, edist (X s ω) (X (f s) ω) = 0 := hX.edist_eq_zero (hf_edist s)
    let g : (s : J) → { t : J // edist s t ≤ δ } → { t : C // edist (f s) t ≤ δ } := by
      refine fun s t ↦ ⟨⟨f' t.1.2, hf'C t.1.2⟩, ?_⟩
      let t' : C := ⟨f' t.1.2, hf'C t.1.2⟩
      suffices edist (f s).1 t'.1 ≤ δ from this
      calc edist (f s).1 t'.1
      _ ≤ edist (f s).1 s.1 + edist s t.1 + edist t.1.1 t' := edist_triangle4 _ _ _ _
      _ ≤ δ := by
        rw [edist_comm]
        simpa [hf_edist s, hf'_edist t.1.2, t'] using t.2
    have hg_edist (s : J) (t : { t : J // edist s t ≤ δ }) : edist t.1.1 (g s t).1 = 0 :=
      hf'_edist t.1.2
    have hgX_edist (s : J) (t : { t : J // edist s t ≤ δ }) :
      ∀ᵐ ω ∂P, edist (X t ω) (X (g s t) ω) = 0 := hX.edist_eq_zero (hg_edist s t)
    have h_edist_le (s : J) (t : { t : J // edist s t ≤ δ }) :
        ∀ᵐ ω ∂P, edist (X s ω) (X t ω) ≤ edist (X (f s) ω) (X (g s t) ω) := by
      filter_upwards [hfX_edist s, hgX_edist s t] with ω h₁ h₂
      calc edist (X s ω) (X t ω)
      _ ≤ edist (X s ω) (X (f s) ω) + edist (X (f s) ω) (X (g s t) ω)
          + edist (X (g s t) ω) (X t ω) := edist_triangle4 _ _ _ _
      _ ≤ edist (X (f s) ω) (X (g s t) ω) := by
        rw [edist_comm (X (g s t) ω)]
        simp [h₁, h₂]
    calc ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P
    _ ≤ ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ }),
        edist (X (f s) ω) (X (g s t) ω) ^ p ∂P := by
      have : Countable J := by simp [hJ.countable]
      have (s : J) : Countable { t : J // edist s t ≤ δ } := Subtype.countable
      simp_rw [← ae_all_iff] at h_edist_le
      refine lintegral_mono_ae ?_
      filter_upwards [h_edist_le] with ω h_edist_le
      gcongr with s t
      · exact hX.p_pos.le
      · exact h_edist_le s t
    _ ≤ ∫⁻ ω, ⨆ (s : C) (t : { t : C // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P := by
      gcongr with ω
      refine iSup_le fun s ↦ iSup_le fun t ↦ ?_
      exact le_iSup_of_le (f s) <| le_iSup_of_le (g s t) le_rfl

lemma exists_nat_pow_lt_iInf (hJ : Metric.ediam J < ∞) (hJ_finite : J.Finite)
    (hJ_nonempty : J.Nonempty) :
    ∃ k : ℕ, Metric.ediam J * 2⁻¹ ^ k < ⨅ (s : J) (t : J) (_h : 0 < edist s t), edist s t := by
  let ε₀ := Metric.ediam J
  suffices 0 < ⨅ (s : J) (t : J) (_h : 0 < edist s t), edist s t by
    suffices ∀ᶠ k in atTop,
        ε₀ * 2⁻¹ ^ k < ⨅ (s : J) (t : J) (_h : 0 < edist s t), edist s t from this.exists
    have h_tendsto : Tendsto (fun n ↦ ε₀ * 2⁻¹ ^ n) atTop (𝓝 0) := by
      rw [← mul_zero (ε₀ : ℝ≥0∞)]
      change Tendsto ((fun p : ℝ≥0∞ × ℝ≥0∞ ↦ p.1 * p.2) ∘ (fun n : ℕ ↦ (ε₀, 2⁻¹ ^ n))) atTop
        (𝓝 (ε₀ * 0))
      refine (ENNReal.tendsto_mul (a := ε₀) (b := 0) (by simp) (.inr hJ.ne)).comp ?_
      refine Tendsto.prodMk_nhds tendsto_const_nhds ?_
      exact ENNReal.tendsto_pow_atTop_nhds_zero_iff.mpr (by simp)
    exact h_tendsto.eventually_lt_const this
  -- `⊢ 0 < ⨅ s, ⨅ t, ⨅ (_ : 0 < edist s t), edist s t`, since `J` is nonempty and finite
  rw [iInf_subtype]
  change 0 < ⨅ s ∈ J, ⨅ (t : J) (_h : 0 < edist s t), edist s t
  rw [hJ_finite.lt_iInf_iff hJ_nonempty]
  intro s hsJ
  rw [iInf_subtype]
  change 0 < ⨅ t ∈ J, ⨅ (_h : 0 < edist s t), edist s t
  rw [hJ_finite.lt_iInf_iff hJ_nonempty]
  intro t htJ
  by_cases hst : 0 < edist s t <;> simp [hst]

theorem _root_.solution (hJ : HasBoundedCoveringNumber J c d)
    (hJ_finite : J.Finite) (hX : IsAEKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hdq_lt : d < q) (hδ_le : Metric.ediam J ≤ δ / 4) :
    ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ}), edist (X s ω) (X t ω) ^ p ∂P
      ≤ 4 ^ p * 2 ^ q * M * c * δ ^ (q - d) * Cp d p q := by
  rcases isEmpty_or_nonempty J with hJ_empty | hJ_nonempty
  · simp
  replace hJ_nonempty : J.Nonempty := Set.nonempty_coe_sort.mp hJ_nonempty
  have hε' : Metric.ediam J < ∞ := hJ.ediam_lt_top
  let ε₀ := (Metric.ediam J).toNNReal
  rcases eq_zero_or_pos ε₀ with hε₀_eq_zero | hε₀_pos
  · simp only [ENNReal.toNNReal_eq_zero_iff, hε'.ne, or_false, ε₀] at hε₀_eq_zero
    suffices ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P = 0
      by simp [this]
    refine hX.lintegral_sup_rpow_edist_eq_zero' hJ_finite.countable ?_
    refine fun s t ↦ le_antisymm ?_ zero_le
    calc edist s t
    _ ≤ Metric.ediam J := Metric.edist_le_ediam_of_mem s.2 t.1.2
    _ = 0 := hε₀_eq_zero
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (ε₀ : ℝ≥0∞) * 2⁻¹ ^ k <
      ⨅ (s : J) (t : J) (_h : 0 < edist s t), edist s t := by
    have := exists_nat_pow_lt_iInf hε' hJ_finite hJ_nonempty
    convert this
    simp [ε₀, ENNReal.coe_toNNReal hε'.ne]
  have hε₀_mul_pos n : 0 < ε₀ * 2⁻¹ ^ n := by positivity
  let C' : ℕ → Set T := fun n ↦ minimalCover (ε₀ * 2⁻¹ ^ n) J
  have hC'_subset n : C' n ⊆ J := minimalCover_subset
  have hC'_fin n : (C' n).Finite := finite_minimalCover
  have hC'_card n : (C' n).encard = coveringNumber (ε₀ * 2⁻¹ ^ n) J :=
    encard_minimalCover (hJ_finite.totallyBounded.coveringNumber_ne_top (by positivity))
  have hC' n : IsCover (ε₀ * 2⁻¹ ^ n) J (C' n) :=
    isCover_minimalCover (hJ_finite.totallyBounded.coveringNumber_ne_top (by positivity))
  let C : ℕ → Finset T := fun n ↦ (hC'_fin n).toFinset
  have hC_subset n : (C n : Set T) ⊆ J := by simpa [C] using hC'_subset n
  have hC_card n : #(C n) = coveringNumber (ε₀ * 2⁻¹ ^ n) J := by
    rw [← hC'_card n]
    simp [C, ← Set.Finite.encard_eq_coe_toFinset_card]
  have hC n : IsCover (ε₀ * 2⁻¹ ^ n) J (C n) := by simpa [C] using hC' n
  -- change the supremum over `J` to a supremum over `C k`
  have hX.q_pos_pos : 0 < q := hd_pos.trans hdq_lt
  rw [← lintegral_sup_cover_eq_of_lt_iInf_dist hX hJ_finite (hC k) (hC_subset k) (δ := δ)]
  swap; · simpa [ENNReal.inv_pow] using hk
  -- change the scale: go to `C 0`.
  refine (scale_change_lintegral_iSup hX δ 0 k).trans ?_
  -- the first term of the sum is zero because `C 0` is a singleton
  have hC_zero : #(C 0) ≤ 1 := by
    suffices (#(C 0) : ℕ∞) = 1 by norm_cast at this; simp [this]
    simp only [hC_card 0, pow_zero, mul_one, ε₀]
    exact coveringNumber_eq_one_of_ediam_le hJ_nonempty (by rw [ENNReal.coe_toNNReal hε'.ne])
  have h_first_eq_zero :
      ∫⁻ ω, ⨆ (s : C k) (t : { t : C k // edist s t ≤ δ }),
          edist (X (chainingSequence C s k 0) ω) (X (chainingSequence C t k 0) ω) ^ p ∂P
        = 0 := by
    refine (lintegral_eq_zero_iff' ?_).mpr (ae_of_all _ fun ω ↦ ?_)
    · refine AEMeasurable.iSup fun s ↦ AEMeasurable.iSup fun t ↦ ?_
      exact hX.aemeasurable_edist.pow_const _
    simp only [Pi.zero_apply, ENNReal.iSup_eq_zero, ENNReal.rpow_eq_zero_iff]
    intro s t
    suffices chainingSequence C s k 0 = chainingSequence C t k 0 by simp [this, hX.p_pos]
    rw [Finset.card_le_one_iff] at hC_zero
    exact hC_zero (chainingSequence_mem hC hJ_nonempty s.2 0 zero_le)
      (chainingSequence_mem hC hJ_nonempty t.1.2 0 zero_le)
  simp only [h_first_eq_zero, mul_zero, zero_add]
  -- the second term is bounded by the result we want
  simp_rw [mul_assoc]
  gcongr
  simp_rw [← mul_assoc]
  refine (second_term_bound hX ?_ hC hC_subset hC_card hdq_lt hJ zero_le).trans ?_
  · simp [ε₀, ENNReal.coe_toNNReal hε'.ne]
  simp only [pow_zero, mul_one]
  have hδ_le' : Metric.ediam J ≤ δ := by
    refine hδ_le.trans ?_
    rw [ENNReal.div_le_iff (by simp) (by simp)]
    conv_lhs => rw [← mul_one δ, ENNReal.coe_mul]
    gcongr
    norm_cast
  simp only [ε₀, ENNReal.coe_toNNReal hε'.ne]
  grw [hδ_le']
  swap; · positivity
  refine le_of_eq ?_
  calc 2 ^ d * M * c * (2 * δ) ^ (q - d) * Cp d p q
  _ = 2 ^ d * 2 ^ (q - d) * M * c * δ ^ (q - d) * Cp d p q := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by bound)]
    ring
  _ = 2 ^ q * M * c * δ ^ (q - d) * Cp d p q := by
    rw [← ENNReal.rpow_add _ _ (by simp) (by simp)]
    ring_nf

