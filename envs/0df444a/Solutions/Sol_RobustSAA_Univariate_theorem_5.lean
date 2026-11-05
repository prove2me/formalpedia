-- Prove2me | solution 1 for RobustSAA.Univariate.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T20:01:56.121725+00:00
-- url     : https://prove2.me/submissions/59fedfb2-0ce3-4e63-ab98-f670dc1b5c3a

import Mathlib
import Definitions.Def_RobustSAA_Univariate_Setting
import Theorems.Thm_RobustSAA_Univariate_levy_metrizes
import Theorems.Thm_RobustSAA_Univariate_levy_empirical_tendsto
import Theorems.Thm_RobustSAA_Univariate_levy_le_ks
import Theorems.Thm_RobustSAA_Univariate_ks_le_kuiper
import Theorems.Thm_RobustSAA_Univariate_ks_sq_le_cvm
import Theorems.Thm_RobustSAA_Univariate_ks_sq_le_ad
import Theorems.Thm_RobustSAA_Univariate_watson_bound
import Theorems.Thm_RobustSAA_Univariate_watson_meanDev_cube

open Filter MeasureTheory RobustSAA.Univariate

namespace RSAA3Red

lemma levySet_nonempty (A B : ℝ → ℝ) (hA : ∀ x, 0 ≤ A x ∧ A x ≤ 1)
    (hB : ∀ x, 0 ≤ B x ∧ B x ≤ 1) :
    ({ε : ℝ | 0 < ε ∧ ∀ ξ : ℝ, A (ξ - ε) - ε ≤ B ξ ∧ B ξ ≤ A (ξ + ε) + ε}).Nonempty := by
  refine ⟨2, by norm_num, fun ξ => ⟨?_, ?_⟩⟩
  · linarith [(hA (ξ - 2)).2, (hB ξ).1]
  · linarith [(hA (ξ + 2)).1, (hB ξ).2]

lemma levyDist_nonneg (A B : ℝ → ℝ) : 0 ≤ levyDist A B :=
  Real.sInf_nonneg (fun _ h => le_of_lt h.1)

lemma levyDist_triangle (A B C : ℝ → ℝ) (hA : ∀ x, 0 ≤ A x ∧ A x ≤ 1)
    (hB : ∀ x, 0 ≤ B x ∧ B x ≤ 1) (hC : ∀ x, 0 ≤ C x ∧ C x ≤ 1) :
    levyDist B C ≤ levyDist A B + levyDist A C := by
  refine le_of_forall_pos_lt_add (fun δ hδ => ?_)
  obtain ⟨e1, he1, he1lt⟩ := exists_lt_of_csInf_lt (levySet_nonempty A B hA hB)
    (show levyDist A B < levyDist A B + δ / 2 by linarith)
  obtain ⟨e2, he2, he2lt⟩ := exists_lt_of_csInf_lt (levySet_nonempty A C hA hC)
    (show levyDist A C < levyDist A C + δ / 2 by linarith)
  have hmem : e1 + e2 ∈ {ε : ℝ | 0 < ε ∧ ∀ ξ : ℝ, B (ξ - ε) - ε ≤ C ξ ∧ C ξ ≤ B (ξ + ε) + ε} := by
    refine ⟨by linarith [he1.1, he2.1], fun ξ => ⟨?_, ?_⟩⟩
    · have h2 := (he2.2 ξ).1
      have h6 : B (ξ - (e1 + e2)) ≤ A (ξ - e2) + e1 := by
        have := (he1.2 (ξ - (e1 + e2))).2
        rwa [show ξ - (e1 + e2) + e1 = ξ - e2 by ring] at this
      linarith
    · have h2 := (he2.2 ξ).2
      have h6 : A (ξ + e2) ≤ B (ξ + (e1 + e2)) + e1 := by
        have := (he1.2 (ξ + (e1 + e2))).1
        rw [show ξ + (e1 + e2) - e1 = ξ + e2 by ring] at this
        linarith
      linarith
  have := csInf_le ⟨0, fun _ h => le_of_lt h.1⟩ hmem
  unfold levyDist at *
  linarith

lemma cdfOf_mem (F : ProbabilityMeasure ℝ) (x : ℝ) : 0 ≤ cdfOf F x ∧ cdfOf F x ≤ 1 := by
  have : IsProbabilityMeasure (F : Measure ℝ) := inferInstance
  exact ⟨ProbabilityTheory.cdf_nonneg _ _, ProbabilityTheory.cdf_le_one _ _⟩

lemma empCdf_mem {N : ℕ} (s : Fin N → ℝ) (x : ℝ) : 0 ≤ empCdf s x ∧ empCdf s x ≤ 1 := by
  unfold empCdf
  refine ⟨by positivity, ?_⟩
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · rw [div_le_one (by exact_mod_cast h)]
    have := Finset.card_filter_le (Finset.univ : Finset (Fin N)) (fun i => s i ≤ x)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this

/-- Generic consistency criterion: if membership in the region forces `d_Lévy(F̂_N, F₀) ≤ b N`
with `b N → 0`, the region is uniformly consistent. -/
lemma consistent_of_bound
    (region : (N : ℕ) → (Fin N → ℝ) → Set (ProbabilityMeasure ℝ)) (b : ℕ → ℝ)
    (hb : Tendsto b atTop (nhds 0))
    (hreg : ∀ N : ℕ, 0 < N → ∀ (s : Fin N → ℝ) (F₀ : ProbabilityMeasure ℝ),
      F₀ ∈ region N s → levyDist (empCdf s) (cdfOf F₀) ≤ b N) :
    IsUniformlyConsistent IsContinuousLaw region := by
  intro F hF
  filter_upwards [levy_empirical_tendsto F hF] with ω hω G hG
  by_contra hcon
  rw [not_frequently] at hcon
  apply hG
  rw [levy_metrizes]
  have hev : ∀ᶠ N in atTop, levyDist (cdfOf (G N)) (cdfOf F) ≤
      b N + levyDist (empCdf (sample ω N)) (cdfOf F) := by
    filter_upwards [hcon, eventually_gt_atTop 0] with N hN hNpos
    have hmem : G N ∈ region N (sample ω N) := not_not.mp hN
    have h1 := hreg N hNpos _ _ hmem
    have h2 := levyDist_triangle (empCdf (sample ω N)) (cdfOf (G N)) (cdfOf F)
      (empCdf_mem _) (cdfOf_mem _) (cdfOf_mem _)
    linarith
  have hlim : Tendsto (fun N => b N + levyDist (empCdf (sample ω N)) (cdfOf F)) atTop
      (nhds 0) := by simpa using hb.add hω
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun N => levyDist_nonneg _ _)) hev

lemma tendsto_inv_sqrt : Tendsto (fun N : ℕ => 1 / Real.sqrt N) atTop (nhds 0) := by
  have h := (tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
  exact h.congr (fun N => by simp)

lemma tendsto_inv_nat : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (nhds 0) := by
  exact (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).congr (fun N => by simp)

/-- `b N = √(max (1/√N + 3/(2N)) (C/√N + a N + 2/√N)) → 0` when `a N → 0`. -/
lemma tendsto_bound (C : ℝ) (a : ℕ → ℝ) (ha : Tendsto a atTop (nhds 0)) :
    Tendsto (fun N : ℕ => Real.sqrt (max (1 / Real.sqrt N + 3 / (2 * N))
      (C / Real.sqrt N + a N + 2 / Real.sqrt N))) atTop (nhds 0) := by
  have h1 := tendsto_inv_sqrt
  have h2 := tendsto_inv_nat
  have hA : Tendsto (fun N : ℕ => 1 / Real.sqrt N + 3 / (2 * N)) atTop (nhds 0) := by
    have : Tendsto (fun N : ℕ => 1 / Real.sqrt N + (3 / 2) * (1 / (N : ℝ))) atTop
        (nhds (0 + (3 / 2) * 0)) := h1.add (h2.const_mul _)
    simp only [mul_zero, add_zero] at this
    refine this.congr (fun N => ?_)
    congr 1
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · field_simp
  have hB : Tendsto (fun N : ℕ => C / Real.sqrt N + a N + 2 / Real.sqrt N) atTop (nhds 0) := by
    have : Tendsto (fun N : ℕ => C * (1 / Real.sqrt N) + a N + 2 * (1 / Real.sqrt N)) atTop
        (nhds (C * 0 + 0 + 2 * 0)) := ((h1.const_mul C).add ha).add (h1.const_mul 2)
    simp only [mul_zero, add_zero] at this
    refine this.congr (fun N => ?_)
    simp [div_eq_mul_inv]
  have := (hA.max hB).sqrt
  simpa using this

lemma levy_le_sqrt_of_ks_sq {N : ℕ} (hN : 0 < N) (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ)
    (B : ℝ) (hB : ksStat F₀ s ^ 2 ≤ B) :
    levyDist (empCdf s) (cdfOf F₀) ≤ Real.sqrt B := by
  have h1 := levy_le_ks hN F₀ s
  have h0 := levyDist_nonneg (empCdf s) (cdfOf F₀)
  have hks : 0 ≤ ksStat F₀ s := le_trans h0 h1
  calc levyDist (empCdf s) (cdfOf F₀) ≤ ksStat F₀ s := h1
    _ = Real.sqrt (ksStat F₀ s ^ 2) := (Real.sqrt_sq hks).symm
    _ ≤ Real.sqrt B := Real.sqrt_le_sqrt hB

lemma sq_le_of_le_rate {x τ q : ℝ} {N : ℕ} (hN : 0 < N) (hx : 0 ≤ x) (hxτ : x ≤ τ)
    (hτ : τ ≤ q / Real.sqrt N) : x ^ 2 ≤ q ^ 2 / N := by
  have hsq : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have h := pow_le_pow_left₀ hx (le_trans hxτ hτ) 2
  rw [div_pow, Real.sq_sqrt (by positivity)] at h
  exact h

lemma sqrtN_mul_le {y q : ℝ} {N : ℕ} (hN : 0 < N) (hy : y ≤ q ^ 2 / N) :
    Real.sqrt N * y ≤ q ^ 2 / Real.sqrt N := by
  have hsq : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hNs : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt (by positivity)).symm
  calc Real.sqrt N * y ≤ Real.sqrt N * (q ^ 2 / N) := mul_le_mul_of_nonneg_left hy hsq.le
    _ = q ^ 2 / Real.sqrt N := by
      have h2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt (by positivity)
      field_simp
      linear_combination q ^ 2 * h2

lemma watson_aux (x q r : ℝ) (hx : 0 ≤ x) (hr : 0 < r) (h : x ^ 3 ≤ 8 * q ^ 2 / r ^ 6) :
    r ^ 3 * x ^ 2 ≤ (1 + 8 * q ^ 2) / r := by
  set y := x * r ^ 2 with hy
  have hy0 : 0 ≤ y := by positivity
  have hy3 : y ^ 3 ≤ 8 * q ^ 2 := by
    have h6 : (0 : ℝ) < r ^ 6 := by positivity
    rw [le_div_iff₀ h6] at h
    rw [hy]; nlinarith [h]
  have hy2 : y ^ 2 ≤ 1 + 8 * q ^ 2 := by
    rcases le_or_gt y 1 with h1 | h1
    · nlinarith [sq_nonneg q]
    · nlinarith [mul_le_mul_of_nonneg_left h1.le (sq_nonneg y)]
  rw [le_div_iff₀ hr]
  have : r ^ 3 * x ^ 2 * r = y ^ 2 := by rw [hy]; ring
  linarith

/-- `r N = N^{1/6}`. -/
noncomputable def r6 (N : ℕ) : ℝ := (N : ℝ) ^ ((6 : ℕ)⁻¹ : ℝ)

lemma r6_pos {N : ℕ} (hN : 0 < N) : 0 < r6 N := Real.rpow_pos_of_pos (by exact_mod_cast hN) _

lemma r6_pow6 (N : ℕ) : r6 N ^ 6 = N :=
  Real.rpow_inv_natCast_pow (by positivity) (by norm_num)

lemma sqrt_eq_r6 (N : ℕ) : Real.sqrt N = r6 N ^ 3 := by
  have h0 : 0 ≤ r6 N := Real.rpow_nonneg (by positivity) _
  rw [← r6_pow6 N, show r6 N ^ 6 = (r6 N ^ 3) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

lemma tendsto_inv_r6 (c : ℝ) : Tendsto (fun N : ℕ => c / r6 N) atTop (nhds 0) := by
  have h1 : Tendsto (fun N : ℕ => r6 N) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have := (tendsto_inv_atTop_zero.comp h1).const_mul c
  simpa [div_eq_mul_inv] using this

end RSAA3Red

open RSAA3Red

theorem solution (τ : ℕ → ℝ) (hτ : ThresholdRate τ) :
    IsUniformlyConsistent IsContinuousLaw (ksRegion τ) ∧
    IsUniformlyConsistent IsContinuousLaw (kuiperRegion τ) ∧
    IsUniformlyConsistent IsContinuousLaw (cvmRegion τ) ∧
    IsUniformlyConsistent IsContinuousLaw (watsonRegion τ) ∧
    IsUniformlyConsistent IsContinuousLaw (adRegion τ) := by
  obtain ⟨q, hq⟩ := hτ
  have hqs : Tendsto (fun N : ℕ => q / Real.sqrt N) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_sqrt.const_mul q
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- KS
    refine consistent_of_bound _ (fun N => q / Real.sqrt N) hqs ?_
    intro N hN s F₀ hmem
    exact le_trans (levy_le_ks hN F₀ s) (le_trans hmem (hq N hN))
  · -- Kuiper
    refine consistent_of_bound _ (fun N => q / Real.sqrt N) hqs ?_
    intro N hN s F₀ hmem
    exact le_trans (levy_le_ks hN F₀ s) (le_trans (ks_le_kuiper hN F₀ s)
      (le_trans hmem (hq N hN)))
  · -- CvM
    refine consistent_of_bound _ _ (tendsto_bound (q ^ 2) (fun _ => 0) tendsto_const_nhds) ?_
    intro N hN s F₀ hmem
    apply levy_le_sqrt_of_ks_sq hN
    refine le_trans (ks_sq_le_cvm hN F₀ s) (max_le_max le_rfl ?_)
    have hc : cvmStat F₀ s ^ 2 ≤ q ^ 2 / N :=
      sq_le_of_le_rate hN (Real.sqrt_nonneg _) hmem (hq N hN)
    have := sqrtN_mul_le hN hc
    simp only [add_zero]
    linarith
  · -- Watson
    refine consistent_of_bound _ _ (tendsto_bound (q ^ 2) _ (tendsto_inv_r6 (1 + 8 * q ^ 2))) ?_
    intro N hN s F₀ hmem
    apply levy_le_sqrt_of_ks_sq hN
    refine le_trans (ks_sq_le_cvm hN F₀ s) (max_le_max le_rfl ?_)
    have hw : watsonStat F₀ s ^ 2 ≤ q ^ 2 / N :=
      sq_le_of_le_rate hN (Real.sqrt_nonneg _) hmem (hq N hN)
    have hid := (watson_bound hN F₀ s).1
    have hcube := watson_meanDev_cube hN F₀ s
    have hr := r6_pos hN
    have hx3 : |meanDev F₀ s| ^ 3 ≤ 8 * q ^ 2 / r6 N ^ 6 := by
      rw [r6_pow6]
      calc |meanDev F₀ s| ^ 3 ≤ 8 * watsonStat F₀ s ^ 2 := hcube
        _ ≤ 8 * (q ^ 2 / N) := by linarith
        _ = 8 * q ^ 2 / N := by ring
    have haux := watson_aux _ _ _ (abs_nonneg _) hr hx3
    rw [sq_abs, ← sqrt_eq_r6] at haux
    have hw' := sqrtN_mul_le hN hw
    have hcvm : cvmStat F₀ s ^ 2 = watsonStat F₀ s ^ 2 + meanDev F₀ s ^ 2 := by linarith
    rw [hcvm, mul_add]
    linarith
  · -- AD
    refine consistent_of_bound _ _ (tendsto_bound (q ^ 2) (fun _ => 0) tendsto_const_nhds) ?_
    intro N hN s F₀ hmem
    have hmem' : adStat F₀ s ≤ ENNReal.ofReal (τ N) := hmem
    unfold adStat at hmem'
    split_ifs at hmem' with hu
    · apply levy_le_sqrt_of_ks_sq hN
      refine le_trans (ks_sq_le_ad hN F₀ s hu) (max_le_max le_rfl ?_)
      have hle : Real.sqrt (adSq F₀ s) ≤ max (τ N) 0 := by
        rcases (ENNReal.ofReal_le_ofReal_iff' ).mp hmem' with h | h
        · exact le_trans h (le_max_left _ _)
        · exact le_trans h (le_max_right _ _)
      have hsq : adSq F₀ s ≤ Real.sqrt (adSq F₀ s) ^ 2 := by
        rcases le_or_gt 0 (adSq F₀ s) with h | h
        · rw [Real.sq_sqrt h]
        · nlinarith [sq_nonneg (Real.sqrt (adSq F₀ s))]
      have hmax : max (τ N) 0 ≤ |q| / Real.sqrt N := by
        have hsq : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
        refine max_le (le_trans (hq N hN) ?_) (by positivity)
        exact div_le_div_of_nonneg_right (le_abs_self q) hsq
      have h2 : Real.sqrt (adSq F₀ s) ^ 2 ≤ |q| ^ 2 / N :=
        sq_le_of_le_rate hN (Real.sqrt_nonneg _) hle hmax
      rw [sq_abs] at h2
      have := sqrtN_mul_le hN (le_trans hsq h2)
      simp only [add_zero]
      linarith
    · exact absurd hmem' (by simp)
