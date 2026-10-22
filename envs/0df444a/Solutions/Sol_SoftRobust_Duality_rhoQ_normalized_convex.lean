-- Prove2me | solution 1 for SoftRobust.Duality.rhoQ_normalized_convex
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:23:22.117741+00:00
-- url     : https://prove2.me/submissions/566e499c-b537-4109-9e5c-13060ed53419

import Mathlib
import Definitions.Def_SoftRobust_Duality_Mixture
import Definitions.Def_SoftRobust_Duality_ConvexRiskMeasure
import Definitions.Def_SoftRobust_Duality_Model

set_option autoImplicit false
open MeasureTheory
open scoped NNReal ENNReal
open SoftRobust.Duality

section SRLib
variable {Ω : Type*} [MeasurableSpace Ω]

lemma srl_int (Q : ProbabilityMeasure Ω) {Y : Ω → ℝ} (hY : IsBddPayoff Y) :
    Integrable Y (Q : Measure Ω) := by
  obtain ⟨hm, C, hC⟩ := hY
  exact Integrable.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall (fun ω => by
    simpa using hC ω))

lemma srl_bound (Q : ProbabilityMeasure Ω) {Y : Ω → ℝ} (C : ℝ) (hC : ∀ ω, |Y ω| ≤ C) :
    |∫ ω, Y ω ∂(Q : Measure Ω)| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := (Q : Measure Ω)) (f := Y) (C := C)
    (Filter.Eventually.of_forall (fun ω => by simpa using hC ω))
  simpa using this

lemma srl_bdd_add {Y : Ω → ℝ} (hY : IsBddPayoff Y) (c : ℝ) : IsBddPayoff (fun ω => Y ω + c) := by
  obtain ⟨hm, C, hC⟩ := hY
  exact ⟨hm.add_const c, C + |c|, fun ω => (abs_add_le _ _).trans (add_le_add (hC ω) le_rfl)⟩

lemma srl_bdd_comb {Y₁ Y₂ : Ω → ℝ} (h₁ : IsBddPayoff Y₁) (h₂ : IsBddPayoff Y₂) (l : ℝ) :
    IsBddPayoff (fun ω => l * Y₁ ω + (1 - l) * Y₂ ω) := by
  obtain ⟨hm1, C1, hC1⟩ := h₁
  obtain ⟨hm2, C2, hC2⟩ := h₂
  refine ⟨(hm1.const_mul l).add (hm2.const_mul (1 - l)), |l| * C1 + |1 - l| * C2, fun ω => ?_⟩
  calc |l * Y₁ ω + (1 - l) * Y₂ ω| ≤ |l * Y₁ ω| + |(1 - l) * Y₂ ω| := abs_add_le _ _
    _ ≤ |l| * C1 + |1 - l| * C2 := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (hC1 ω) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hC2 ω) (abs_nonneg _))

lemma srl_zero_mem {𝒬 : ℝ≥0 → Set (ProbabilityMeasure Ω)} (h𝒬 : IsAdmissibleFamily 𝒬) :
    ∃ Q : ProbabilityMeasure Ω, penaltyOfFamily 𝒬 Q = 0 := by
  obtain ⟨Q, hQ⟩ := h𝒬.zero_nonempty
  refine ⟨Q, le_antisymm ?_ zero_le⟩
  unfold penaltyOfFamily
  exact (iInf₂_le (0 : ℝ≥0) hQ).trans (by simp)

lemma srl_pv_nonempty {𝒬 : ℝ≥0 → Set (ProbabilityMeasure Ω)} (h𝒬 : IsAdmissibleFamily 𝒬)
    (Y : Ω → ℝ) : (penaltyValues (penaltyOfFamily 𝒬) Y).Nonempty := by
  obtain ⟨Q, hQ⟩ := srl_zero_mem h𝒬
  exact ⟨_, Q, by simp [hQ], rfl⟩

lemma srl_pv_bdd (α : ProbabilityMeasure Ω → ℝ≥0∞) {Y : Ω → ℝ} (C : ℝ) (hC : ∀ ω, |Y ω| ≤ C) :
    BddAbove (penaltyValues α Y) := by
  refine ⟨C, ?_⟩
  rintro r ⟨Q, -, rfl⟩
  have := srl_bound Q C hC
  have h2 := (abs_le.mp this).1
  have h3 : 0 ≤ (α Q).toReal := ENNReal.toReal_nonneg
  linarith


lemma srl_mix_zero (Q₁ Q₂ : ProbabilityMeasure Ω) (ht : (0 : ℝ≥0) ≤ 1) : mix 0 ht Q₁ Q₂ = Q₂ := by
  apply Subtype.ext
  show (((0 : ℝ≥0) : ℝ≥0∞) • (Q₁ : Measure Ω) + (((1 - 0 : ℝ≥0)) : ℝ≥0∞) • (Q₂ : Measure Ω)) = (Q₂ : Measure Ω)
  simp

lemma srl_mix_one (Q₁ Q₂ : ProbabilityMeasure Ω) (ht : (1 : ℝ≥0) ≤ 1) : mix 1 ht Q₁ Q₂ = Q₁ := by
  apply Subtype.ext
  show (((1 : ℝ≥0) : ℝ≥0∞) • (Q₁ : Measure Ω) + (((1 - 1 : ℝ≥0)) : ℝ≥0∞) • (Q₂ : Measure Ω)) = (Q₁ : Measure Ω)
  simp

lemma srl_convex_pen {𝒬 : ℝ≥0 → Set (ProbabilityMeasure Ω)} (h𝒬 : IsAdmissibleFamily 𝒬) :
    IsConvexPenalty (penaltyOfFamily 𝒬) := by
  intro t ht Q₁ Q₂
  by_cases h0 : t = 0
  · subst h0; rw [srl_mix_zero]; simp
  by_cases h1 : t = 1
  · subst h1; rw [srl_mix_one]; simp
  have hs0 : (1 - t : ℝ≥0) ≠ 0 := by
    intro h; apply h1; exact le_antisymm ht (tsub_eq_zero_iff_le.mp h)
  by_cases ha₁ : penaltyOfFamily 𝒬 Q₁ = ⊤
  · rw [ha₁, ENNReal.mul_top (by exact_mod_cast h0)]; simp
  by_cases ha₂ : penaltyOfFamily 𝒬 Q₂ = ⊤
  · rw [ha₂, ENNReal.mul_top (by exact_mod_cast hs0)]; simp
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hb
  have hε' : (ε : ℝ≥0∞) ≠ 0 := by exact_mod_cast hε.ne'
  have h1' : penaltyOfFamily 𝒬 Q₁ < penaltyOfFamily 𝒬 Q₁ + ε := ENNReal.lt_add_right ha₁ hε'
  have h2' : penaltyOfFamily 𝒬 Q₂ < penaltyOfFamily 𝒬 Q₂ + ε := ENNReal.lt_add_right ha₂ hε'
  have h1'' : (⨅ (e : ℝ≥0) (_ : Q₁ ∈ 𝒬 e), (e : ℝ≥0∞)) < penaltyOfFamily 𝒬 Q₁ + ε := h1'
  have h2'' : (⨅ (e : ℝ≥0) (_ : Q₂ ∈ 𝒬 e), (e : ℝ≥0∞)) < penaltyOfFamily 𝒬 Q₂ + ε := h2'
  obtain ⟨e₁, h1''⟩ := iInf_lt_iff.mp h1''
  obtain ⟨e₂, h2''⟩ := iInf_lt_iff.mp h2''
  obtain ⟨hq₁, h1''⟩ := iInf_lt_iff.mp h1''
  obtain ⟨hq₂, h2''⟩ := iInf_lt_iff.mp h2''
  have hmem := h𝒬.convex e₁ e₂ Q₁ Q₂ t ht hq₁ hq₂
  have hle : penaltyOfFamily 𝒬 (mix t ht Q₁ Q₂) ≤ ((t * e₁ + (1 - t) * e₂ : ℝ≥0) : ℝ≥0∞) := by
    unfold penaltyOfFamily
    exact iInf₂_le (t * e₁ + (1 - t) * e₂) hmem
  have hsum : (t : ℝ≥0∞) + ((1 - t : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [← ENNReal.coe_add, add_tsub_cancel_of_le ht]; simp
  calc penaltyOfFamily 𝒬 (mix t ht Q₁ Q₂) ≤ ((t * e₁ + (1 - t) * e₂ : ℝ≥0) : ℝ≥0∞) := hle
    _ = (t : ℝ≥0∞) * e₁ + ((1 - t : ℝ≥0) : ℝ≥0∞) * e₂ := by push_cast; rfl
    _ ≤ (t : ℝ≥0∞) * (penaltyOfFamily 𝒬 Q₁ + ε) + ((1 - t : ℝ≥0) : ℝ≥0∞) * (penaltyOfFamily 𝒬 Q₂ + ε) := by
        gcongr
    _ = (t : ℝ≥0∞) * penaltyOfFamily 𝒬 Q₁ + ((1 - t : ℝ≥0) : ℝ≥0∞) * penaltyOfFamily 𝒬 Q₂ + ε := by
        rw [mul_add, mul_add]
        calc _ = (t : ℝ≥0∞) * penaltyOfFamily 𝒬 Q₁ + ((1 - t : ℝ≥0) : ℝ≥0∞) * penaltyOfFamily 𝒬 Q₂ +
              ((t : ℝ≥0∞) + ((1 - t : ℝ≥0) : ℝ≥0∞)) * ε := by ring
          _ = _ := by rw [hsum, one_mul]

end SRLib

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (𝒬 : ℝ≥0 → Set (ProbabilityMeasure Ω)) (h𝒬 : IsAdmissibleFamily 𝒬) :
    IsConvexRiskMeasure (rhoQ 𝒬) ∧ IsGeneratedBy (rhoQ 𝒬) (penaltyOfFamily 𝒬) ∧
      IsNormalizedPenalty (penaltyOfFamily 𝒬) := by
  have hbdd : ∀ Y : Ω → ℝ, IsBddPayoff Y → BddAbove (penaltyValues (penaltyOfFamily 𝒬) Y) :=
    fun Y hY => srl_pv_bdd _ hY.2.choose hY.2.choose_spec
  have hle : ∀ Y : Ω → ℝ, IsBddPayoff Y → ∀ Q : ProbabilityMeasure Ω, penaltyOfFamily 𝒬 Q ≠ ⊤ →
      -(∫ ω, Y ω ∂(Q : Measure Ω)) - (penaltyOfFamily 𝒬 Q).toReal ≤ rhoQ 𝒬 Y :=
    fun Y hY Q hQ => le_csSup (hbdd Y hY) ⟨Q, hQ, rfl⟩
  have hsup : ∀ (Y : Ω → ℝ) (r : ℝ), (∀ Q : ProbabilityMeasure Ω, penaltyOfFamily 𝒬 Q ≠ ⊤ →
      -(∫ ω, Y ω ∂(Q : Measure Ω)) - (penaltyOfFamily 𝒬 Q).toReal ≤ r) → rhoQ 𝒬 Y ≤ r := by
    intro Y r h
    exact csSup_le (srl_pv_nonempty h𝒬 Y) (by rintro _ ⟨Q, hQ, rfl⟩; exact h Q hQ)
  have hadd : ∀ (Y : Ω → ℝ), IsBddPayoff Y → ∀ (c : ℝ) (Q : ProbabilityMeasure Ω),
      ∫ ω, (Y ω + c) ∂(Q : Measure Ω) = (∫ ω, Y ω ∂(Q : Measure Ω)) + c := by
    intro Y hY c Q
    rw [integral_add (srl_int Q hY) (integrable_const c)]
    simp
  have hcomb : ∀ (Y₁ Y₂ : Ω → ℝ), IsBddPayoff Y₁ → IsBddPayoff Y₂ → ∀ (l : ℝ) (Q : ProbabilityMeasure Ω),
      ∫ ω, (l * Y₁ ω + (1 - l) * Y₂ ω) ∂(Q : Measure Ω) =
        l * (∫ ω, Y₁ ω ∂(Q : Measure Ω)) + (1 - l) * ∫ ω, Y₂ ω ∂(Q : Measure Ω) := by
    intro Y₁ Y₂ h₁ h₂ l Q
    rw [integral_add ((srl_int Q h₁).const_mul l) ((srl_int Q h₂).const_mul (1 - l)),
      integral_const_mul, integral_const_mul]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨srl_convex_pen h𝒬, fun Y hY => isLUB_csSup (srl_pv_nonempty h𝒬 Y) (hbdd Y hY)⟩,
    srl_zero_mem h𝒬⟩
  · intro Y₁ Y₂ h₁ h₂ hY
    refine hsup Y₁ _ (fun Q hQ => ?_)
    have := hle Y₂ h₂ Q hQ
    have hint : ∫ ω, Y₂ ω ∂(Q : Measure Ω) ≤ ∫ ω, Y₁ ω ∂(Q : Measure Ω) :=
      integral_mono (srl_int Q h₂) (srl_int Q h₁) (fun ω => hY ω)
    linarith
  · intro Y c hY
    apply le_antisymm
    · refine hsup _ _ (fun Q hQ => ?_)
      have := hle Y hY Q hQ
      rw [hadd Y hY c Q]
      linarith
    · have h2 : rhoQ 𝒬 Y ≤ rhoQ 𝒬 (fun ω => Y ω + c) + c := by
        refine hsup Y _ (fun Q hQ => ?_)
        have := hle _ (srl_bdd_add hY c) Q hQ
        rw [hadd Y hY c Q] at this
        linarith
      linarith
  · intro Y₁ Y₂ h₁ h₂ l hl0 hl1
    refine hsup _ _ (fun Q hQ => ?_)
    have a1 := hle Y₁ h₁ Q hQ
    have a2 := hle Y₂ h₂ Q hQ
    rw [hcomb Y₁ Y₂ h₁ h₂ l Q]
    have hl1' : 0 ≤ 1 - l := by linarith
    nlinarith [mul_le_mul_of_nonneg_left a1 hl0, mul_le_mul_of_nonneg_left a2 hl1']
