-- Prove2me | solution 1 for ReferralPriority.Optimal.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T12:13:19.703809+00:00
-- url     : https://prove2.me/submissions/625d28fb-aeca-420c-8e3a-64314b72ce71

import Mathlib
import Definitions.Def_ReferralPriority_Optimal_Model
import Theorems.Thm_ReferralPriority_Optimal_proposition_1_i
import Theorems.Thm_ReferralPriority_Optimal_first_best_achievability
import Theorems.Thm_ReferralPriority_Optimal_gcubic_unique_root
import Theorems.Thm_ReferralPriority_Optimal_cutoff
import Theorems.Thm_ReferralPriority_Optimal_eq_A1
import Theorems.Thm_ReferralPriority_Optimal_relaxation_bound
import Theorems.Thm_ReferralPriority_Optimal_eq_A6_strict

open ReferralPriority.Optimal

/-- Partial/full priority regime: when (A.3) holds, the Proposition 4 (i) tuple achieves the first best. -/
theorem rp4_fb_of_ge (E : Env) (hS : E.Standing) (hk : E.k < E.V - E.c / E.mu) (rs : ℝ)
    (hrs : rs ∈ Set.Ioo (0 : ℝ) 1) (hg : gcubic E rs = 0) (Lam : ℝ) (hL0 : 0 < Lam)
    (hL1 : Lam < E.mu - E.c / E.V) (hge : Lstar E rs ≤ Lam) :
    AchievesFB E Lam (W1pp E Lam) (W0pp E Lam) (rFB E Lam) 1 ∧
      WorkConserving E Lam (W1pp E Lam) (W0pp E Lam) (rFB E Lam) 1 ∧
      (OA6bBinding E Lam (W1pp E Lam) (rFB E Lam) 1 ↔ Lam = Lstar E rs) ∧
      W1pp E Lam < W0pp E Lam := by
  obtain ⟨hmu, hc, hkpos, hV⟩ := hS
  have cut := (cutoff E ⟨hmu, hc, hkpos, hV⟩ hk rs hrs hg).2.2.2 Lam hL0 hL1
  have fba := first_best_achievability E ⟨hmu, hc, hkpos, hV⟩ Lam hL0 hL1
  have p1 := proposition_1_i E ⟨hmu, hc, hkpos, hV⟩ Lam hL0 hL1
  obtain ⟨W1, W0, hW⟩ := fba.1.mpr (cut.1.mpr hge)
  obtain ⟨e1, e0⟩ := fba.2 W1 W0 hW
  subst e1 e0
  refine ⟨⟨hW, p1.2.1⟩, ?_, ?_, ?_⟩
  · unfold WorkConserving W1pp W0pp
    simp only [mul_one]
    have key : ∀ x r : ℝ, r * (x - E.k * (1 - r) / E.c) + (1 - r) * (x + E.k * r / E.c) = x := by
      intro x r; field_simp; ring
    exact key _ _
  · unfold OA6bBinding
    simp only [mul_one, one_pow]
    rw [eq_comm]
    exact cut.2
  · unfold W1pp W0pp
    have : 0 < E.k * (1 - rFB E Lam) / E.c + E.k * rFB E Lam / E.c := by
      rw [← add_div]; apply div_pos _ hc; nlinarith
    linarith

/-- Strategic-delay regime. -/
theorem rp4_sd_of_lt (E : Env) (hS : E.Standing) (hk : E.k < E.V - E.c / E.mu) (rs : ℝ)
    (hrs : rs ∈ Set.Ioo (0 : ℝ) 1) (hg : gcubic E rs = 0) (Lam : ℝ) (hL0 : 0 < Lam)
    (hL1 : Lam < E.mu - E.c / E.V) (hlt : Lam < Lstar E rs) :
    ¬ FBAchievable E Lam ∧
      SBOptimal E Lam (W1sd E Lam) (W0sd E Lam) (rSB E Lam) 1 ∧
      StrategicDelay E Lam (W1sd E Lam) (W0sd E Lam) (rSB E Lam) 1 ∧
      OA6bBinding E Lam (W1sd E Lam) (rSB E Lam) 1 := by
  have hS' := hS
  obtain ⟨hmu, hc, hkpos, hV⟩ := hS
  have cut := (cutoff E hS' hk rs hrs hg).2.2.2 Lam hL0 hL1
  have fba := first_best_achievability E hS' Lam hL0 hL1
  have p1 := proposition_1_i E hS' Lam hL0 hL1
  have rb := relaxation_bound E hS' hk Lam hL0
  obtain ⟨hr0, hr1⟩ := rb.1
  obtain ⟨hD, hA6⟩ := eq_A6_strict E hS' hk rs hrs hg Lam hL0 hlt
  -- ¬ FBAchievable
  refine ⟨?_, ?_⟩
  · rintro ⟨W1, W0, r, α, hSB, hG⟩
    have heq : throughput Lam r α = throughput Lam (rFB E Lam) 1 := hG.unique p1.2.1
    obtain ⟨hα, hr, -⟩ := p1.2.2 W1 W0 r α hSB.1 heq
    subst hα hr
    have := cut.1.mp (fba.1.mp ⟨W1, W0, hSB⟩)
    linarith
  -- basic facts on the strategic-delay tuple
  have hcm : 0 < E.c / E.mu := div_pos hc hmu
  have hVk : 0 < E.V - E.k := by linarith
  set r := rSB E Lam with hr_def
  have hkey : E.mu * (1 - r) - Lam * r = E.c / (E.V - E.k) := by
    rw [hr_def]; unfold rSB
    have : E.mu + Lam ≠ 0 := by linarith
    field_simp
    ring
  have hW1 : W1sd E Lam = (E.V - E.k) / E.c := by
    unfold W1sd; rw [← hr_def, hkey]; field_simp
  have hW0 : W0sd E Lam = (E.V - E.k) / E.c + E.k / E.c := by
    unfold W0sd; rw [hW1]
  set D := E.mu * (1 - r) - Lam with hD_def
  -- 1/D < (V - r k)/c
  have hlt1 : 1 / D < (E.V - r * E.k) / E.c := by
    have h1 : E.c / D < E.V - r * E.k := by linarith
    rw [div_lt_div_iff₀ hD hc]
    rw [div_lt_iff₀ hD] at h1
    linarith
  have hrhs : r * 1 * W1sd E Lam + (1 - r * 1) * W0sd E Lam = (E.V - r * E.k) / E.c := by
    rw [hW1, hW0]; field_simp; ring
  have hpay : ∀ r' : ℝ, payoff E (W1sd E Lam) (W0sd E Lam) 1 r' = 0 := by
    intro r'; unfold payoff; rw [hW1, hW0]; field_simp; ring
  have hOA6a : ¬ WorkConserving E Lam (W1sd E Lam) (W0sd E Lam) r 1 := by
    unfold WorkConserving
    rw [hrhs]; simp only [mul_one]; rw [← hD_def]; exact ne_of_gt hlt1
  have hB : OA6bBinding E Lam (W1sd E Lam) r 1 := by
    unfold OA6bBinding; simp only [mul_one, one_pow]; rfl
  have hfeas : SBFeasible E Lam (W1sd E Lam) (W0sd E Lam) r 1 := by
    have hW1n : 0 ≤ W1sd E Lam := by rw [hW1]; positivity
    refine ⟨⟨hW1n, ?_, ⟨hr0.le, hr1.le⟩, ⟨zero_le_one, le_rfl⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hW0]; positivity
    · unfold IR; rw [hpay]
    · unfold OA6a; rw [hrhs]; simp only [mul_one]; rw [← hD_def]; exact hlt1.le
    · unfold OA6b; rw [← hB]
    · unfold OA6c
      have hDle : D ≤ E.mu - Lam * 1 := by rw [hD_def]; nlinarith
      have h2 : 1 / (E.mu - Lam * 1) ≤ 1 / D := one_div_le_one_div_of_le hD hDle
      have h3 : (E.V - r * E.k) / E.c ≤ W0sd E Lam := by
        rw [hW0, ← add_div]; apply div_le_div_of_nonneg_right _ hc.le; nlinarith
      linarith
    · unfold Stable; simp only [mul_one]; linarith
    · intro r' _; rw [hpay, hpay]
  refine ⟨⟨hfeas, ⟨⟨_, _, _, _, hfeas, rfl⟩, ?_⟩⟩, hOA6a, hB⟩
  rintro x ⟨W1, W0, r', α, hF, rfl⟩
  have hF' := hF
  obtain ⟨⟨-, -, ⟨hr'0, hr'1⟩, ⟨hα0, hα1⟩, -, -, -, -, hst⟩, -⟩ := hF
  rcases hr'0.lt_or_eq with hr'p | hr'z
  · rcases hα0.lt_or_eq with hαp | hαz
    · exact rb.2 r' α ⟨hr'p, hr'1⟩ ⟨hαp, hα1⟩ hst
        (eq_A1 E hS' Lam hL0 W1 W0 r' α hF' hr'p hαp)
    · subst hαz
      unfold throughput; simp only [mul_zero, sub_zero, zero_div]
      simp only [mul_one]
      apply div_nonneg <;> linarith
  · subst hr'z
    unfold throughput
    simp only [zero_mul, sub_zero, div_one, mul_one]
    rw [le_div_iff₀ (by linarith)]
    have h1 : α * (1 - r) ≤ 1 := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 hL0.le
    nlinarith

theorem solution (E : Env) (hS : E.Standing) (hk : E.k < E.V - E.c / E.mu) :
    ∃! Ls : ℝ, 0 < Ls ∧ Ls < E.mu - E.c / E.V ∧
      ∀ Lam : ℝ, 0 < Lam → Lam < E.mu - E.c / E.V →
        (Ls < Lam →
            AchievesFB E Lam (W1pp E Lam) (W0pp E Lam) (rFB E Lam) 1 ∧
            PartialPriority E Lam (W1pp E Lam) (W0pp E Lam) (rFB E Lam) 1) ∧
        (Lam = Ls →
            AchievesFB E Lam (W1pp E Lam) (W0pp E Lam) (rFB E Lam) 1 ∧
            FullPriority E Lam (W1pp E Lam) (W0pp E Lam) (rFB E Lam) 1) ∧
        (Lam < Ls →
            ¬ FBAchievable E Lam ∧
            SBOptimal E Lam (W1sd E Lam) (W0sd E Lam) (rSB E Lam) 1 ∧
            StrategicDelay E Lam (W1sd E Lam) (W0sd E Lam) (rSB E Lam) 1 ∧
            OA6bBinding E Lam (W1sd E Lam) (rSB E Lam) 1) := by
  obtain ⟨rs, hrs, hg, -, -, -⟩ := gcubic_unique_root E hS hk
  have cut := cutoff E hS hk rs hrs hg
  refine ⟨Lstar E rs, ⟨cut.1, cut.2.1, fun Lam h0 h1 => ⟨?_, ?_, ?_⟩⟩, ?_⟩
  · intro hgt
    obtain ⟨hA, hW, hB, hlt⟩ := rp4_fb_of_ge E hS hk rs hrs hg Lam h0 h1 hgt.le
    exact ⟨hA, hW, fun h => absurd (hB.mp h) (ne_of_gt hgt), hlt⟩
  · intro heq
    obtain ⟨hA, hW, hB, -⟩ := rp4_fb_of_ge E hS hk rs hrs hg Lam h0 h1 heq.ge
    exact ⟨hA, hW, hB.mpr heq⟩
  · intro hlt
    exact rp4_sd_of_lt E hS hk rs hrs hg Lam h0 h1 hlt
  · rintro Ls ⟨h0', h1', hP⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · -- Ls < Lstar
      have hm0 : 0 < (Ls + Lstar E rs) / 2 := by linarith [cut.1]
      have hm1 : (Ls + Lstar E rs) / 2 < E.mu - E.c / E.V := by linarith [cut.2.1]
      have hA := ((hP _ hm0 hm1).1 (by linarith)).1
      exact (rp4_sd_of_lt E hS hk rs hrs hg _ hm0 hm1 (by linarith)).1 ⟨_, _, _, _, hA⟩
    · have hm0 : 0 < (Ls + Lstar E rs) / 2 := by linarith [cut.1]
      have hm1 : (Ls + Lstar E rs) / 2 < E.mu - E.c / E.V := by linarith [cut.2.1]
      have hA := (rp4_fb_of_ge E hS hk rs hrs hg _ hm0 hm1 (by linarith)).1
      exact ((hP _ hm0 hm1).2.2 (by linarith)).1 ⟨_, _, _, _, hA⟩
