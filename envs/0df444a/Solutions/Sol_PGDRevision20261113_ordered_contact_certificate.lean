-- Prove2me | solution 1 for PGDRevision20261113.ordered_contact_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-13T09:58:00.13417+00:00
-- url     : https://prove2.me/submissions/ebf623cc-8b9e-41ba-b3e9-873ec98c8973

import Theorems.Thm_PGDRevision20261113_ordered_kernel_ratio
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1500000
open PGDRevision20261113
open scoped ENNReal

private lemma kernel_pos (G : GeometryData) (hG : AdmissibleGeometry G)
    (c t : ℝ) (ht : t ∈ geometryDomain G) : 0 < geometryKernel G c t := by
  cases hf : G.family with
  | interval beta =>
    have htd : t ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [geometryDomain, hf] using ht
    simp only [geometryKernel, hf]
    unfold powerCurvature
    exact div_pos (add_pos (Real.rpow_pos_of_pos (by linarith [htd.1]) _)
      (Real.rpow_pos_of_pos (by linarith [htd.2]) _)) (by norm_num)
  | realLine =>
    rcases hG with ⟨_, _, _, _, hG⟩
    simp only [hf] at hG
    have hb : 0 < G.b t := by
      by_cases ht0 : t = 0
      · subst t
        rw [hG.2.2.1]
        norm_num
      · linarith [hG.2.2.2.1 t ht0]
    simpa [geometryKernel, hf] using Real.rpow_pos_of_pos hb c

private lemma error_le_iff (A B v w : ℝ) (hA : 0 ≤ A) (hB : 0 < B)
    (hv : 0 < v) (hw : 0 < w) :
    (v - A) / (v + B) ≤ (w - A) / (w + B) ↔ v ≤ w := by
  rw [div_le_div_iff₀ (by linarith : 0 < v + B) (by linarith : 0 < w + B)]
  constructor
  · intro h
    by_contra hn
    have hp := mul_pos (by linarith : 0 < A + B) (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith
  · intro h
    have hp := mul_nonneg (by linarith : 0 ≤ A + B) (sub_nonneg.mpr h)
    nlinarith

private lemma error_bound (G : GeometryData) (w : ℝ × ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hw : geometryRho G w.1 w.2 ≤ ENNReal.ofReal r)
    (t : ℝ) (ht : t ∈ geometryDomain G) : |geometryError G w.1 w.2 t| ≤ r := by
  have hs : ENNReal.ofReal |geometryError G w.1 w.2 t| ≤ geometryRho G w.1 w.2 :=
    le_iSup_of_le t (le_iSup_of_le ht le_rfl)
  exact (ENNReal.ofReal_le_ofReal_iff hr).mp (hs.trans hw)

private lemma contact_rho (G : GeometryData) (z : ℝ × ℝ) (r : ℝ) (hr : 0 < r)
    (henv : UniformGeometryEnvelope G z r) (hc : ThreeFeatureContacts G z r) :
    geometryRho G z.1 z.2 = ENNReal.ofReal r := by
  apply le_antisymm
  · exact iSup_le fun t => iSup_le fun ht => ENNReal.ofReal_le_ofReal (henv t ht)
  · rcases hc with ⟨t, sigma, ht, hs, h01, h12, he⟩
    have h0 := he 0
    have habs : |geometryError G z.1 z.2 (t 0)| = r := by
      rcases hs with rfl | rfl
      · simpa [alternatingSign, abs_of_pos hr] using congrArg abs h0
      · simpa [alternatingSign, abs_of_pos hr] using congrArg abs h0
    rw [← habs]
    exact le_iSup_of_le (t 0) (le_iSup_of_le (ht 0) le_rfl)

private lemma competitor_eq (G : GeometryData) (hG : AdmissibleGeometry G)
    (z w : ℝ × ℝ) (hz : FeasiblePair z) (hw : FeasiblePair w)
    (r : ℝ) (hr : 0 < r) (hc : ThreeFeatureContacts G z r)
    (hwr : geometryRho G w.1 w.2 ≤ ENNReal.ofReal r) : w = z := by
  rcases hc with ⟨t, sigma, ht, hs, h01, h12, he⟩
  have hB (i : Fin 3) : 0 < G.lambda * G.b (t i) := by
    have hk := kernel_pos G hG (matchedExponent G) (t i) (ht i)
    rcases hG with ⟨hl, _, _, _, hfam⟩
    cases hf : G.family with
    | interval beta =>
      simp only [hf] at hfam
      rw [hfam.2.1 (t i) (ht i)]
      exact mul_pos hl (by simpa [geometryKernel, matchedExponent, hf] using hk)
    | realLine =>
      simp only [hf] at hfam
      have hb : 0 < G.b (t i) := by
        by_cases hi : t i = 0
        · rw [hi, hfam.2.2.1]; norm_num
        · linarith [hfam.2.2.2.1 (t i) hi]
      exact mul_pos hl hb
  have hvz (i : Fin 3) : 0 < z.2 * geometryKernel G z.1 (t i) :=
    mul_pos hz.2 (kernel_pos G hG _ _ (ht i))
  have hvw (i : Fin 3) : 0 < w.2 * geometryKernel G w.1 (t i) :=
    mul_pos hw.2 (kernel_pos G hG _ _ (ht i))
  have horder (i : Fin 3) :
      (alternatingSign sigma i = 1 →
        w.2 * geometryKernel G w.1 (t i) ≤ z.2 * geometryKernel G z.1 (t i)) ∧
      (alternatingSign sigma i = -1 →
        z.2 * geometryKernel G z.1 (t i) ≤ w.2 * geometryKernel G w.1 (t i)) := by
    have hew := abs_le.mp (error_bound G w r hr.le hwr (t i) (ht i))
    constructor
    · intro hi
      have hez : geometryError G z.1 z.2 (t i) = r := by simpa [hi] using he i
      apply (error_le_iff _ _ _ _ (hG.2.1 _ (ht i)) (hB i) (hvw i) (hvz i)).mp
      change geometryError G w.1 w.2 (t i) ≤ geometryError G z.1 z.2 (t i)
      rw [hez]
      exact hew.2
    · intro hi
      have hez : geometryError G z.1 z.2 (t i) = -r := by simpa [hi] using he i
      apply (error_le_iff _ _ _ _ (hG.2.1 _ (ht i)) (hB i) (hvz i) (hvw i)).mp
      change geometryError G z.1 z.2 (t i) ≤ geometryError G w.1 w.2 (t i)
      rw [hez]
      exact hew.1
  have hp (i : Fin 3) (hi : alternatingSign sigma i = 1) :
      w.2 * geometryKernel G w.1 (t i) / (z.2 * geometryKernel G z.1 (t i)) ≤ 1 := by
    exact (div_le_iff₀ (hvz i)).mpr (by simpa using (horder i).1 hi)
  have hn (i : Fin 3) (hi : alternatingSign sigma i = -1) :
      1 ≤ w.2 * geometryKernel G w.1 (t i) / (z.2 * geometryKernel G z.1 (t i)) := by
    exact (le_div_iff₀ (hvz i)).mpr (by simpa using (horder i).2 hi)
  have hrp (i : Fin 3) (hi : alternatingSign sigma i = 1) :
      1 ≤ z.2 * geometryKernel G z.1 (t i) / (w.2 * geometryKernel G w.1 (t i)) := by
    exact (le_div_iff₀ (hvw i)).mpr (by simpa using (horder i).1 hi)
  have hrn (i : Fin 3) (hi : alternatingSign sigma i = -1) :
      z.2 * geometryKernel G z.1 (t i) / (w.2 * geometryKernel G w.1 (t i)) ≤ 1 := by
    exact (div_le_iff₀ (hvw i)).mpr (by simpa using (horder i).2 hi)
  have hczw : ¬ z.1 < w.1 := by
    intro hcw
    have hmono := PGDRevision20261113.ordered_kernel_ratio G hG z.1 w.1 z.2 w.2
      hz.1 hcw hz.2 hw.2
    rcases hs with rfl | rfl
    · have hm := hmono (t 1) (ht 1) (t 2) (ht 2) h12
      have ha := hn 1 (by norm_num [alternatingSign] <;> decide)
      have hb := hp 2 (by norm_num [alternatingSign] <;> decide)
      linarith
    · have hm := hmono (t 0) (ht 0) (t 1) (ht 1) h01
      have ha := hn 0 (by norm_num [alternatingSign] <;> decide)
      have hb := hp 1 (by norm_num [alternatingSign] <;> decide)
      linarith
  have hcwz : ¬ w.1 < z.1 := by
    intro hcw
    have hmono := PGDRevision20261113.ordered_kernel_ratio G hG w.1 z.1 w.2 z.2
      hw.1 hcw hw.2 hz.2
    rcases hs with rfl | rfl
    · have hm := hmono (t 0) (ht 0) (t 1) (ht 1) h01
      have ha := hrp 0 (by norm_num [alternatingSign] <;> decide)
      have hb := hrn 1 (by norm_num [alternatingSign] <;> decide)
      linarith
    · have hm := hmono (t 1) (ht 1) (t 2) (ht 2) h12
      have ha := hrp 1 (by norm_num [alternatingSign] <;> decide)
      have hb := hrn 2 (by norm_num [alternatingSign] <;> decide)
      linarith
  have hceq : w.1 = z.1 := le_antisymm (le_of_not_gt hczw) (le_of_not_gt hcwz)
  have hpeq : w.2 = z.2 := by
    have hk0 := kernel_pos G hG z.1 (t 0) (ht 0)
    have hk1 := kernel_pos G hG z.1 (t 1) (ht 1)
    rcases hs with rfl | rfl
    · have ha := (horder 0).1 (by norm_num [alternatingSign] <;> decide)
      have hb := (horder 1).2 (by norm_num [alternatingSign] <;> decide)
      rw [hceq] at ha hb
      exact le_antisymm ((mul_le_mul_iff_left₀ hk0).mp ha) ((mul_le_mul_iff_left₀ hk1).mp hb)
    · have ha := (horder 1).1 (by norm_num [alternatingSign] <;> decide)
      have hb := (horder 0).2 (by norm_num [alternatingSign] <;> decide)
      rw [hceq] at ha hb
      exact le_antisymm ((mul_le_mul_iff_left₀ hk1).mp ha) ((mul_le_mul_iff_left₀ hk0).mp hb)
  exact Prod.ext hceq hpeq

theorem solution : OrderedContactCertificateClaim := by
  intro G hG z r hz hr henv hc
  have hrho := contact_rho G z r hr henv hc
  have heq (w : ℝ × ℝ) (hw : FeasiblePair w)
      (hwr : geometryRho G w.1 w.2 ≤ geometryRho G z.1 z.2) : w = z :=
    competitor_eq G hG z w hz hw r hr hc (hwr.trans_eq hrho)
  have hopt : GeometryOptimum G z := by
    refine ⟨hz, ?_⟩
    intro w hw
    by_contra hn
    have hlt := lt_of_not_ge hn
    have hwz := heq w hw hlt.le
    subst w
    exact (lt_irrefl _) hlt
  refine ⟨hopt, hrho, ?_⟩
  intro w hw
  exact heq w hw.1 (hw.2 z hz)
