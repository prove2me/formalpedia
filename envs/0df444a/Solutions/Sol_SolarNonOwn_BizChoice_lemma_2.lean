-- Prove2me | solution 1 for SolarNonOwn.BizChoice.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T11:16:58.002639+00:00
-- url     : https://prove2.me/submissions/b526bf70-36e7-4835-895a-d5be40182481

import Mathlib
import Definitions.Def_SolarNonOwn_BizChoice_ClosedForms

noncomputable section
open MeasureTheory
open SolarNonOwn.BizChoice

/-- Customer choice does not depend on the demand level `d`: every expected cost
contains the same term `r * d`. -/
private lemma choice_d (prm : Params) (x : Prices) (η d : ℝ) :
    choice prm x η d = choice prm x η 0 := by
  have hc : ∀ i, cost prm x η d i = cost prm x η 0 i + prm.r * d := by
    intro i; cases i <;> simp only [cost] <;> ring
  unfold choice
  simp only [hc, add_lt_add_iff_right, add_le_add_iff_right]

/-- Adoption equals the normalized Lebesgue measure of the choice set inside `[0,g]`. -/
private lemma adoption_eq (prm : Params) (h : Measure ℝ) [IsProbabilityMeasure h]
    (hg : 0 < prm.g) (x : Prices) (i : BizOpt) :
    adoption prm h x i =
      (1 / prm.g) * (volume ({η | choice prm x η 0 = i} ∩ Set.Icc 0 prm.g)).toReal := by
  have hset : {z : ℝ × ℝ | choice prm x z.1 z.2 = i} =
      {η | choice prm x η 0 = i} ×ˢ (Set.univ : Set ℝ) := by
    ext ⟨η, d⟩
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, and_true]
    rw [choice_d]
  unfold adoption population
  rw [hset, Measure.prod_prod, measure_univ, mul_one, Measure.smul_apply,
    Measure.restrict_apply' measurableSet_Icc, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]

/-- Sandwich: a set between `(a,b)` and `[a,b] ∪ {0}` has length `b - a`. -/
private lemma vol_sandwich (E : Set ℝ) (a b : ℝ)
    (h1 : Set.Ioo a b ⊆ E) (h2 : E ⊆ Set.Icc a b ∪ {0}) :
    volume E = ENNReal.ofReal (b - a) := by
  apply le_antisymm
  · calc volume E ≤ volume (Set.Icc a b ∪ {0}) := measure_mono h2
      _ ≤ volume (Set.Icc a b) + volume ({0} : Set ℝ) := measure_union_le _ _
      _ = ENNReal.ofReal (b - a) := by rw [Real.volume_Icc, Real.volume_singleton, add_zero]
  · calc ENNReal.ofReal (b - a) = volume (Set.Ioo a b) := (Real.volume_Ioo).symm
      _ ≤ volume E := measure_mono h1

/-- The decision rule `choice`, unfolded into cost comparisons. -/
private lemma choice_iff (prm : Params) (x : Prices) (η d : ℝ) :
    (choice prm x η d = .S ↔
      ¬(cost prm x η d .U < cost prm x η d .S ∧ cost prm x η d .U < cost prm x η d .L ∧
        cost prm x η d .U < cost prm x η d .P) ∧
      (cost prm x η d .S ≤ cost prm x η d .L ∧ cost prm x η d .S ≤ cost prm x η d .P)) ∧
    (choice prm x η d = .L ↔
      ¬(cost prm x η d .U < cost prm x η d .S ∧ cost prm x η d .U < cost prm x η d .L ∧
        cost prm x η d .U < cost prm x η d .P) ∧
      ¬(cost prm x η d .S ≤ cost prm x η d .L ∧ cost prm x η d .S ≤ cost prm x η d .P) ∧
      cost prm x η d .L ≤ cost prm x η d .P) ∧
    (choice prm x η d = .P ↔
      ¬(cost prm x η d .U < cost prm x η d .S ∧ cost prm x η d .U < cost prm x η d .L ∧
        cost prm x η d .U < cost prm x η d .P) ∧
      ¬(cost prm x η d .S ≤ cost prm x η d .L ∧ cost prm x η d .S ≤ cost prm x η d .P) ∧
      ¬(cost prm x η d .L ≤ cost prm x η d .P)) ∧
    (choice prm x η d = .U ↔
      (cost prm x η d .U < cost prm x η d .S ∧ cost prm x η d .U < cost prm x η d .L ∧
        cost prm x η d .U < cost prm x η d .P)) := by
  unfold choice
  split_ifs with h1 h2 h3 <;> simp_all

theorem solution (prm : Params) (h : Measure ℝ) [IsProbabilityMeasure h]
    (hh : h (Set.Iic 0) = 0) (hs : ModelAssumptions prm) (x : Prices) :
    (0 < x.p → x.p ≤ prm.r →
      0 ≤ eta2 x.l x.p → eta2 x.l x.p ≤ eta1 prm x.s x.l →
      eta1 prm x.s x.l ≤ prm.g →
      (∀ η d : ℝ, eta1 prm x.s x.l < η → η ≤ prm.g → choice prm x η d = .S) ∧
      (∀ η d : ℝ, eta2 x.l x.p < η → η < eta1 prm x.s x.l → choice prm x η d = .L) ∧
      (∀ η d : ℝ, 0 < η → η < eta2 x.l x.p → choice prm x η d = .P) ∧
      adoption prm h x .S = 1 - eta1 prm x.s x.l / prm.g ∧
      adoption prm h x .L = (eta1 prm x.s x.l - eta2 x.l x.p) / prm.g ∧
      adoption prm h x .P = eta2 x.l x.p / prm.g) ∧
    (prm.r < x.p →
      0 ≤ eta3 prm x.l → eta3 prm x.l ≤ eta1 prm x.s x.l →
      eta1 prm x.s x.l ≤ prm.g →
      (∀ η d : ℝ, eta1 prm x.s x.l < η → η ≤ prm.g → choice prm x η d = .S) ∧
      (∀ η d : ℝ, eta3 prm x.l < η → η < eta1 prm x.s x.l → choice prm x η d = .L) ∧
      (∀ η d : ℝ, 0 < η → η < eta3 prm x.l → choice prm x η d = .U) ∧
      adoption prm h x .S = 1 - eta1 prm x.s x.l / prm.g ∧
      adoption prm h x .L = (eta1 prm x.s x.l - eta3 prm x.l) / prm.g ∧
      adoption prm h x .P = 0) := by
  obtain ⟨hα, hβ, ht, htr, hg⟩ := hs
  have hr : 0 < prm.r := lt_trans ht htr
  -- costs at d = 0
  have eS : ∀ η, cost prm x η 0 .S = (1 - prm.alpha) * x.s - (prm.r + prm.beta) * η := by
    intro η; simp only [cost]; ring
  have eL : ∀ η, cost prm x η 0 .L = x.l - prm.r * η := by intro η; simp only [cost]; ring
  have eP : ∀ η, cost prm x η 0 .P = (x.p - prm.r) * η := by intro η; simp only [cost]; ring
  have eU : ∀ η, cost prm x η 0 .U = 0 := by intro η; simp only [cost]; ring
  set e1 := eta1 prm x.s x.l with he1
  have hσ : (1 - prm.alpha) * x.s = x.l + prm.beta * e1 := by
    rw [he1]; simp only [eta1]; field_simp; ring
  have hgi : ∀ E : Set ℝ, (1 / prm.g) * (volume E).toReal = (volume E).toReal / prm.g := by
    intro E; ring
  constructor
  · intro hp0 hpr h20 h21 h1g
    set e2 := eta2 x.l x.p with he2
    have hl : x.l = x.p * e2 := by rw [he2]; simp only [eta2]; field_simp
    have cS : ∀ η, cost prm x η 0 .S = x.p * (e2 - η) + prm.beta * (e1 - η) + (x.p - prm.r) * η := by
      intro η; rw [eS, hσ, hl]; ring
    have cL : ∀ η, cost prm x η 0 .L = x.p * (e2 - η) + (x.p - prm.r) * η := by
      intro η; rw [eL, hl]; ring
    have notU : ∀ η, 0 ≤ η → ¬(cost prm x η 0 .U < cost prm x η 0 .S ∧
        cost prm x η 0 .U < cost prm x η 0 .L ∧ cost prm x η 0 .U < cost prm x η 0 .P) := by
      intro η hη ⟨_, _, h3⟩
      rw [eU, eP] at h3
      nlinarith
    have clS : ∀ η, e1 < η → η ≤ prm.g → choice prm x η 0 = .S := by
      intro η h1 _
      refine (choice_iff prm x η 0).1.2 ⟨notU η (by linarith), ?_, ?_⟩
      · rw [cS, cL]; nlinarith [mul_pos hβ (sub_pos.mpr h1)]
      · rw [cS, eP]; nlinarith [mul_pos hβ (sub_pos.mpr h1), mul_pos hp0 (show 0 < η - e2 by linarith)]
    have clL : ∀ η, e2 < η → η < e1 → choice prm x η 0 = .L := by
      intro η h1 h2
      refine (choice_iff prm x η 0).2.1.2 ⟨notU η (by linarith), ?_, ?_⟩
      · rintro ⟨h3, -⟩
        rw [cS, cL] at h3; nlinarith [mul_pos hβ (sub_pos.mpr h2)]
      · rw [cL, eP]; nlinarith [mul_pos hp0 (sub_pos.mpr h1)]
    have clP : ∀ η, 0 < η → η < e2 → choice prm x η 0 = .P := by
      intro η h1 h2
      refine (choice_iff prm x η 0).2.2.1.2 ⟨notU η h1.le, ?_, ?_⟩
      · rintro ⟨-, h3⟩
        rw [cS, eP] at h3
        nlinarith [mul_pos hp0 (sub_pos.mpr h2), mul_pos hβ (show 0 < e1 - η by linarith)]
      · intro h3
        rw [cL, eP] at h3; nlinarith [mul_pos hp0 (sub_pos.mpr h2)]
    -- choice sets inside [0,g]
    have vS : volume ({η | choice prm x η 0 = .S} ∩ Set.Icc 0 prm.g) = ENNReal.ofReal (prm.g - e1) := by
      apply vol_sandwich
      · intro η hη
        exact ⟨clS η hη.1 hη.2.le, by linarith [hη.1], hη.2.le⟩
      · rintro η ⟨h1, -, h3⟩
        left
        refine ⟨?_, h3⟩
        have := ((choice_iff prm x η 0).1.1 h1).2.1
        rw [cS, cL] at this
        by_contra hc; push Not at hc
        nlinarith [mul_pos hβ (sub_pos.mpr hc)]
    have vL : volume ({η | choice prm x η 0 = .L} ∩ Set.Icc 0 prm.g) = ENNReal.ofReal (e1 - e2) := by
      apply vol_sandwich
      · intro η hη
        exact ⟨clL η hη.1 hη.2, by linarith [hη.1], by linarith [hη.2]⟩
      · rintro η ⟨h1, -, h3⟩
        left
        have hL := ((choice_iff prm x η 0).2.1.1 h1).2.2
        rw [cL, eP] at hL
        refine ⟨?_, ?_⟩
        · by_contra hc; push Not at hc
          nlinarith [mul_pos hp0 (sub_pos.mpr hc)]
        · by_contra hc; push Not at hc
          have := clS η hc h3
          exact absurd (this.symm.trans h1) (by decide)
    have vP : volume ({η | choice prm x η 0 = .P} ∩ Set.Icc 0 prm.g) = ENNReal.ofReal (e2 - 0) := by
      apply vol_sandwich
      · intro η hη
        exact ⟨clP η hη.1 hη.2, hη.1.le, by linarith [hη.2]⟩
      · rintro η ⟨h1, h2, -⟩
        left
        have hP := ((choice_iff prm x η 0).2.2.1.1 h1).2.2
        rw [cL, eP] at hP
        refine ⟨h2, ?_⟩
        by_contra hc; push Not at hc
        nlinarith [mul_pos hp0 (sub_pos.mpr hc)]
    refine ⟨fun η d h1 h2 => by rw [choice_d]; exact clS η h1 h2,
      fun η d h1 h2 => by rw [choice_d]; exact clL η h1 h2,
      fun η d h1 h2 => by rw [choice_d]; exact clP η h1 h2, ?_, ?_, ?_⟩
    · rw [adoption_eq prm h hg, vS, ENNReal.toReal_ofReal (by linarith)]; field_simp
    · rw [adoption_eq prm h hg, vL, ENNReal.toReal_ofReal (by linarith)]; ring
    · rw [adoption_eq prm h hg, vP, ENNReal.toReal_ofReal (by linarith)]; ring
  · intro hpr h30 h31 h1g
    set e3 := eta3 prm x.l with he3
    have hl : x.l = prm.r * e3 := by rw [he3]; simp only [eta3]; field_simp
    have cS : ∀ η, cost prm x η 0 .S = prm.r * (e3 - η) + prm.beta * (e1 - η) := by
      intro η; rw [eS, hσ, hl]; ring
    have cL : ∀ η, cost prm x η 0 .L = prm.r * (e3 - η) := by
      intro η; rw [eL, hl]; ring
    have hpr' : 0 < x.p - prm.r := by linarith
    have clS : ∀ η, e1 < η → η ≤ prm.g → choice prm x η 0 = .S := by
      intro η h1 _
      refine (choice_iff prm x η 0).1.2 ⟨?_, ?_, ?_⟩
      · rintro ⟨h3, -, -⟩
        rw [eU, cS] at h3
        nlinarith [mul_pos hβ (sub_pos.mpr h1), mul_pos hr (show 0 < η - e3 by linarith)]
      · rw [cS, cL]; nlinarith [mul_pos hβ (sub_pos.mpr h1)]
      · rw [cS, eP]
        nlinarith [mul_pos hβ (sub_pos.mpr h1), mul_pos hr (show 0 < η - e3 by linarith),
          mul_pos hpr' (show 0 < η by linarith)]
    have clL : ∀ η, e3 < η → η < e1 → choice prm x η 0 = .L := by
      intro η h1 h2
      refine (choice_iff prm x η 0).2.1.2 ⟨?_, ?_, ?_⟩
      · rintro ⟨-, h3, -⟩
        rw [eU, cL] at h3
        nlinarith [mul_pos hr (sub_pos.mpr h1)]
      · rintro ⟨h3, -⟩
        rw [cS, cL] at h3; nlinarith [mul_pos hβ (sub_pos.mpr h2)]
      · rw [cL, eP]
        nlinarith [mul_pos hr (sub_pos.mpr h1), mul_pos hpr' (show 0 < η by linarith)]
    have clU : ∀ η, 0 < η → η < e3 → choice prm x η 0 = .U := by
      intro η h1 h2
      refine (choice_iff prm x η 0).2.2.2.2 ⟨?_, ?_, ?_⟩
      · rw [eU, cS]
        nlinarith [mul_pos hr (sub_pos.mpr h2), mul_nonneg hβ.le (show 0 ≤ e1 - η by linarith)]
      · rw [eU, cL]; nlinarith [mul_pos hr (sub_pos.mpr h2)]
      · rw [eU, eP]; nlinarith [mul_pos hpr' h1]
    have vS : volume ({η | choice prm x η 0 = .S} ∩ Set.Icc 0 prm.g) = ENNReal.ofReal (prm.g - e1) := by
      apply vol_sandwich
      · intro η hη
        exact ⟨clS η hη.1 hη.2.le, by linarith [hη.1], hη.2.le⟩
      · rintro η ⟨h1, -, h3⟩
        left
        refine ⟨?_, h3⟩
        have := ((choice_iff prm x η 0).1.1 h1).2.1
        rw [cS, cL] at this
        by_contra hc; push Not at hc
        nlinarith [mul_pos hβ (sub_pos.mpr hc)]
    have vL : volume ({η | choice prm x η 0 = .L} ∩ Set.Icc 0 prm.g) = ENNReal.ofReal (e1 - e3) := by
      apply vol_sandwich
      · intro η hη
        exact ⟨clL η hη.1 hη.2, by linarith [hη.1], by linarith [hη.2]⟩
      · rintro η ⟨h1, h2, h3⟩
        rcases eq_or_lt_of_le h2 with h0 | h0
        · right; exact h0.symm
        left
        refine ⟨?_, ?_⟩
        · by_contra hc; push Not at hc
          have := clU η h0 hc
          exact absurd (this.symm.trans h1) (by decide)
        · by_contra hc; push Not at hc
          have := clS η hc h3
          exact absurd (this.symm.trans h1) (by decide)
    have vP : volume ({η | choice prm x η 0 = .P} ∩ Set.Icc 0 prm.g) = 0 := by
      apply measure_mono_null (t := ({0} : Set ℝ)) _ (Real.volume_singleton)
      rintro η ⟨h1, h2, -⟩
      rcases eq_or_lt_of_le h2 with h0 | h0
      · exact h0.symm
      exfalso
      obtain ⟨hU, hS, hLP⟩ := (choice_iff prm x η 0).2.2.1.1 h1
      have cPpos : 0 < cost prm x η 0 .P := by rw [eP]; exact mul_pos hpr' h0
      push Not at hLP
      apply hU
      rw [eU]
      refine ⟨?_, by linarith, cPpos⟩
      by_contra hc; push Not at hc
      apply hS
      constructor <;> linarith
    refine ⟨fun η d h1 h2 => by rw [choice_d]; exact clS η h1 h2,
      fun η d h1 h2 => by rw [choice_d]; exact clL η h1 h2,
      fun η d h1 h2 => by rw [choice_d]; exact clU η h1 h2, ?_, ?_, ?_⟩
    · rw [adoption_eq prm h hg, vS, ENNReal.toReal_ofReal (by linarith)]; field_simp
    · rw [adoption_eq prm h hg, vL, ENNReal.toReal_ofReal (by linarith)]; ring
    · rw [adoption_eq prm h hg, vP, ENNReal.toReal_zero, mul_zero]
