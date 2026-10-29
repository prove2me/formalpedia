-- Prove2me | solution 1 for WangGreenTech.Regulation.lemma_O2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:09:39.033188+00:00
-- url     : https://prove2.me/submissions/a2dbeac5-019d-4288-acac-69bb54fea2a4

import Definitions.Def_WangGreenTech_Regulation_Policies

set_option autoImplicit false

open WangGreenTech.Regulation
open Set

lemma s225mb_cb_nonneg (ε C r : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hr : 0 < r) :
    ∀ y ∈ thresholdRatios ε C r, 0 ≤ y := by
  rintro y (⟨t, ⟨ht0, ht1⟩, rfl⟩ | ⟨s, ⟨hs0, hs1⟩, rfl⟩)
  · have : 0 ≤ t ^ r := Real.rpow_nonneg ht0.le r
    exact div_nonneg (by positivity) ht0.le
  · have : s ^ r ≤ 1 := Real.rpow_le_one hs0 hs1.le hr.le
    have h2 : 0 ≤ C * (1 - s ^ r) := mul_nonneg hC (by linarith)
    exact div_nonneg (by linarith) (by linarith)

lemma s225mb_cb_bdd (ε C r : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hr : 0 < r) :
    BddBelow (thresholdRatios ε C r) :=
  ⟨0, fun y hy => s225mb_cb_nonneg ε C r hε hC hr y hy⟩

lemma s225mb_cb_mem0 (ε C r : ℝ) (hr : 0 < r) :
    2 * ε + C ∈ thresholdRatios ε C r := by
  right
  refine ⟨0, ⟨le_refl _, zero_lt_one⟩, ?_⟩
  simp [Real.zero_rpow hr.ne']

lemma s225mb_cb_le (ε C r : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hr : 0 < r) :
    competitionBound ε C r ≤ 2 * ε + C :=
  csInf_le (s225mb_cb_bdd ε C r hε hC hr) (s225mb_cb_mem0 ε C r hr)

lemma s225mb_cb_eps (ε ε' C r : ℝ) (hε : 0 < ε) (hεε : ε < ε') (hC : 0 ≤ C) (hr : 0 < r) :
    competitionBound ε C r + 2 * (ε' - ε) ≤ competitionBound ε' C r := by
  have hbdd := s225mb_cb_bdd ε C r hε.le hC hr
  unfold competitionBound
  refine le_csInf ⟨_, s225mb_cb_mem0 ε' C r hr⟩ ?_
  rintro y (⟨t, ⟨ht0, ht1⟩, rfl⟩ | ⟨s, ⟨hs0, hs1⟩, rfl⟩)
  · have hI : sInf (thresholdRatios ε C r) ≤ (2 * ε + C * t ^ r) / t :=
      csInf_le hbdd (Or.inl ⟨t, ⟨ht0, ht1⟩, rfl⟩)
    have he : (2 * ε' + C * t ^ r) / t = (2 * ε + C * t ^ r) / t + 2 * (ε' - ε) / t := by
      field_simp; ring
    have hg : 2 * (ε' - ε) ≤ 2 * (ε' - ε) / t := by
      rw [le_div_iff₀ ht0]; nlinarith
    linarith
  · have hI : sInf (thresholdRatios ε C r) ≤ (2 * ε + C * (1 - s ^ r)) / (1 - s) :=
      csInf_le hbdd (Or.inr ⟨s, ⟨hs0, hs1⟩, rfl⟩)
    have hu : 0 < 1 - s := by linarith
    have he : (2 * ε' + C * (1 - s ^ r)) / (1 - s) =
        (2 * ε + C * (1 - s ^ r)) / (1 - s) + 2 * (ε' - ε) / (1 - s) := by
      field_simp; ring
    have hg : 2 * (ε' - ε) ≤ 2 * (ε' - ε) / (1 - s) := by
      rw [le_div_iff₀ hu]; nlinarith
    linarith

lemma s225mb_cb_C (ε C C' r : ℝ) (hε : 0 < ε) (hC : 0 ≤ C) (hCC : C < C') (hr : 0 < r) :
    competitionBound ε C r < competitionBound ε C' r := by
  have hbdd := s225mb_cb_bdd ε C r hε.le hC hr
  have hIle := s225mb_cb_le ε C r hε.le hC hr
  set I := competitionBound ε C r with hIdef
  set t0 : ℝ := 2 * ε / (2 * ε + C + 1) with ht0def
  have ht0pos : 0 < t0 := by positivity
  have ht0lt : t0 < 1 := by rw [ht0def, div_lt_one (by positivity)]; linarith
  have h2t0 : 2 * ε / t0 = 2 * ε + C + 1 := by
    rw [ht0def]; field_simp
  have hp1 : 0 < t0 ^ r := Real.rpow_pos_of_pos ht0pos r
  have hp2 : (1 - t0) ^ r < 1 := Real.rpow_lt_one (by linarith) (by linarith) hr
  set δ : ℝ := min 1 ((C' - C) * min (t0 ^ r) (1 - (1 - t0) ^ r)) with hδ
  have hmin : 0 < min (t0 ^ r) (1 - (1 - t0) ^ r) := lt_min hp1 (by linarith)
  have hδpos : 0 < δ := lt_min one_pos (mul_pos (by linarith) hmin)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ (C' - C) * t0 ^ r :=
    (min_le_right _ _).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith))
  have hδ3 : δ ≤ (C' - C) * (1 - (1 - t0) ^ r) :=
    (min_le_right _ _).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith))
  -- small denominators
  have hsmall : ∀ u a : ℝ, 0 < u → u < t0 → 2 * ε ≤ a → I + δ ≤ a / u := by
    intro u a hu hut ha
    have h1 : 2 * ε / t0 ≤ 2 * ε / u :=
      div_le_div_of_nonneg_left (by linarith) hu hut.le
    have h2 : 2 * ε / u ≤ a / u := div_le_div_of_nonneg_right ha hu.le
    linarith
  have key : I + δ ≤ competitionBound ε C' r := by
    refine le_csInf ⟨_, s225mb_cb_mem0 ε C' r hr⟩ ?_
    rintro y (⟨t, ⟨ht0, ht1⟩, rfl⟩ | ⟨s, ⟨hs0, hs1⟩, rfl⟩)
    · have htr : 0 ≤ t ^ r := Real.rpow_nonneg ht0.le r
      rcases lt_or_ge t t0 with h | h
      · exact hsmall t _ ht0 h (by nlinarith)
      · have hI : I ≤ (2 * ε + C * t ^ r) / t :=
          csInf_le hbdd (Or.inl ⟨t, ⟨ht0, ht1⟩, rfl⟩)
        have he : (2 * ε + C' * t ^ r) / t =
            (2 * ε + C * t ^ r) / t + (C' - C) * t ^ r / t := by
          field_simp; ring
        have hg : (C' - C) * t ^ r ≤ (C' - C) * t ^ r / t := by
          rw [le_div_iff₀ ht0]
          have : 0 ≤ (C' - C) * t ^ r := mul_nonneg (by linarith) htr
          nlinarith
        have hmono : t0 ^ r ≤ t ^ r := Real.rpow_le_rpow ht0pos.le h hr.le
        have : (C' - C) * t0 ^ r ≤ (C' - C) * t ^ r :=
          mul_le_mul_of_nonneg_left hmono (by linarith)
        linarith
    · have hu : 0 < 1 - s := by linarith
      have hsr : s ^ r ≤ 1 := Real.rpow_le_one hs0 hs1.le hr.le
      rcases lt_or_ge (1 - s) t0 with h | h
      · exact hsmall (1 - s) _ hu h (by nlinarith)
      · have hI : I ≤ (2 * ε + C * (1 - s ^ r)) / (1 - s) :=
          csInf_le hbdd (Or.inr ⟨s, ⟨hs0, hs1⟩, rfl⟩)
        have he : (2 * ε + C' * (1 - s ^ r)) / (1 - s) =
            (2 * ε + C * (1 - s ^ r)) / (1 - s) + (C' - C) * (1 - s ^ r) / (1 - s) := by
          field_simp; ring
        have hg : (C' - C) * (1 - s ^ r) ≤ (C' - C) * (1 - s ^ r) / (1 - s) := by
          rw [le_div_iff₀ hu]
          have : 0 ≤ (C' - C) * (1 - s ^ r) := mul_nonneg (by linarith) (by linarith)
          nlinarith
        have hmono : s ^ r ≤ (1 - t0) ^ r := Real.rpow_le_rpow hs0 (by linarith) hr.le
        have : (C' - C) * (1 - (1 - t0) ^ r) ≤ (C' - C) * (1 - s ^ r) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        linarith
  linarith

theorem solution (q r : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hr : 0 < r) :
    (∀ d : ℝ, 0 < d → StrictMonoOn (fun ε => competitionBound ε ((1 - q) * d) r) (Ioi 0)) ∧
    (∀ ε : ℝ, 0 < ε → StrictMonoOn (fun d => competitionBound ε ((1 - q) * d) r) (Ioi 0)) := by
  have hq : 0 < 1 - q := by linarith
  constructor
  · intro d hd a ha b hb hab
    have hC : 0 ≤ (1 - q) * d := (mul_pos hq hd).le
    have := s225mb_cb_eps a b ((1 - q) * d) r ha hab hC hr
    simp only
    linarith
  · intro ε hε a ha b hb hab
    exact s225mb_cb_C ε ((1 - q) * a) ((1 - q) * b) r hε (mul_pos hq ha).le
      (mul_lt_mul_of_pos_left hab hq) hr
