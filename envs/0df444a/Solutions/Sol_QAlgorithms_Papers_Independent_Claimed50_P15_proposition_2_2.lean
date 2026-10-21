-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P15.proposition_2_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T12:59:38.995978+00:00
-- url     : https://prove2.me/submissions/7bd537f4-b48f-40e0-a3a6-69e5c19e3d86

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15
noncomputable section
open Filter MeasureTheory Topology
open QAlgorithms.Papers.Independent.Claimed50.P15

namespace G59H

def G (e : ℝ → ℝ) (r s : ℝ) : ℝ := (-s * r - e s) / (1 - s)

def S (e : ℝ → ℝ) (r : ℝ) : Set EReal := {v | ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ v = ((G e r s : ℝ) : EReal)}

lemma psi_eq (e : ℝ → ℝ) (r : ℝ) : hoeffdingTransform e r = - sSup (S e r) := rfl

lemma S_ge (e : ℝ → ℝ) (r : ℝ) : ((-e 0 : ℝ) : EReal) ≤ sSup (S e r) :=
  le_sSup ⟨0, le_rfl, one_pos, by simp [G]⟩

lemma sup_ne_bot (e : ℝ → ℝ) (r : ℝ) : sSup (S e r) ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (S_ge e r)

lemma psi_ne_top (e : ℝ → ℝ) (r : ℝ) : hoeffdingTransform e r ≠ ⊤ := by
  rw [psi_eq, Ne, EReal.neg_eq_top_iff]; exact sup_ne_bot e r

lemma sup_anti (e : ℝ → ℝ) {r r' : ℝ} (h : r ≤ r') : sSup (S e r') ≤ sSup (S e r) := by
  apply sSup_le
  rintro _ ⟨s, h0, h1, rfl⟩
  apply le_sSup_of_le (show ((G e r s : ℝ) : EReal) ∈ S e r from ⟨s, h0, h1, rfl⟩)
  rw [EReal.coe_le_coe_iff]
  unfold G
  apply div_le_div_of_nonneg_right _ (by linarith)
  nlinarith

lemma mono (e : ℝ → ℝ) : Monotone (hoeffdingTransform e) := by
  intro r r' h
  rw [psi_eq, psi_eq, EReal.neg_le_neg_iff]
  exact sup_anti e h

/-- bounded above when `-e 1 < r` -/
lemma sup_bdd (e : ℝ → ℝ) (hcont : ContinuousOn e (Set.Icc (0 : ℝ) 1)) {r : ℝ} (hr : -e 1 < r) :
    ∃ M : ℝ, sSup (S e r) ≤ (M : EReal) := by
  set h : ℝ → ℝ := fun s => -s * r - e s with hh
  have hc : ContinuousOn h (Set.Icc (0 : ℝ) 1) :=
    ((continuousOn_id.neg).mul continuousOn_const).sub hcont
  have h1 : h 1 < 0 := by simp only [hh]; linarith
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hcw := hc 1 ⟨zero_le_one, le_rfl⟩
  rw [Metric.continuousWithinAt_iff] at hcw
  obtain ⟨δ, hδ, hδh⟩ := hcw (-h 1) (by linarith)
  set d := min (δ / 2) (1 / 2) with hd
  have hd0 : 0 < d := by positivity
  have hdδ : d < δ := by have := min_le_left (δ / 2) (1 / 2); linarith
  refine ⟨|K| / d, sSup_le ?_⟩
  rintro _ ⟨s, h0, h1', rfl⟩
  rw [EReal.coe_le_coe_iff]
  have hs1 : 0 < 1 - s := by linarith
  have hM : 0 ≤ |K| / d := by positivity
  show h s / (1 - s) ≤ |K| / d
  rcases le_or_gt (h s) 0 with hn | hp
  · exact le_trans (div_nonpos_of_nonpos_of_nonneg hn hs1.le) hM
  · have hfar : d ≤ 1 - s := by
      by_contra hc'
      push Not at hc'
      have hdist : dist s 1 < δ := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_pos hs1]; linarith
      have := hδh ⟨h0, h1'.le⟩ hdist
      rw [Real.dist_eq] at this
      have := (abs_lt.1 this).2
      linarith
    have hKs : h s ≤ |K| := le_trans (le_abs_self _) (le_trans (hK s ⟨h0, h1'.le⟩) (le_abs_self K))
    calc h s / (1 - s) ≤ |K| / (1 - s) := div_le_div_of_nonneg_right hKs hs1.le
      _ ≤ |K| / d := div_le_div_of_nonneg_left (abs_nonneg K) hd0 hfar

lemma finite (e : ℝ → ℝ) (hcont : ContinuousOn e (Set.Icc (0 : ℝ) 1)) {r : ℝ} (hr : -e 1 < r) :
    hoeffdingTransform e r = (((hoeffdingTransform e r).toReal : ℝ) : EReal) := by
  obtain ⟨M, hM⟩ := sup_bdd e hcont hr
  have hnb : hoeffdingTransform e r ≠ ⊥ := by
    rw [psi_eq, Ne, EReal.neg_eq_bot_iff]
    exact ne_top_of_le_ne_top (EReal.coe_ne_top M) hM
  exact (EReal.coe_toReal (psi_ne_top e r) hnb).symm

lemma concave (e : ℝ → ℝ) (r q u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (u : EReal) * hoeffdingTransform e r + ((1 - u : ℝ) : EReal) * hoeffdingTransform e q ≤
      hoeffdingTransform e (u * r + (1 - u) * q) := by
  rcases hu0.eq_or_lt with h0 | h0
  · subst h0; simp
  rcases hu1.eq_or_lt with h1 | h1
  · subst h1; simp
  have hu' : (0 : ℝ) < 1 - u := by linarith
  by_cases hr : sSup (S e r) = ⊤
  · rw [psi_eq e r, hr, EReal.neg_top, EReal.mul_bot_of_pos (by exact_mod_cast h0), EReal.bot_add]
    exact bot_le
  by_cases hq : sSup (S e q) = ⊤
  · rw [psi_eq e q, hq, EReal.neg_top, EReal.mul_bot_of_pos (by exact_mod_cast hu'), EReal.add_bot]
    exact bot_le
  set a := (sSup (S e r)).toReal
  set b := (sSup (S e q)).toReal
  have ha : sSup (S e r) = (a : EReal) := (EReal.coe_toReal hr (sup_ne_bot e r)).symm
  have hb : sSup (S e q) = (b : EReal) := (EReal.coe_toReal hq (sup_ne_bot e q)).symm
  have hm : sSup (S e (u * r + (1 - u) * q)) ≤ ((u * a + (1 - u) * b : ℝ) : EReal) := by
    apply sSup_le
    rintro _ ⟨s, hs0, hs1, rfl⟩
    have hra : ((G e r s : ℝ) : EReal) ≤ a := ha ▸ le_sSup ⟨s, hs0, hs1, rfl⟩
    have hqb : ((G e q s : ℝ) : EReal) ≤ b := hb ▸ le_sSup ⟨s, hs0, hs1, rfl⟩
    rw [EReal.coe_le_coe_iff] at hra hqb ⊢
    have : G e (u * r + (1 - u) * q) s = u * G e r s + (1 - u) * G e q s := by
      unfold G
      have : (1 - s) ≠ 0 := by linarith
      field_simp
      ring
    rw [this]
    nlinarith
  rw [psi_eq, psi_eq, psi_eq, ha, hb]
  calc (u : EReal) * -(a : EReal) + ((1 - u : ℝ) : EReal) * -(b : EReal)
      = ((-(u * a + (1 - u) * b) : ℝ) : EReal) := by
        rw [← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
        congr 1; ring
    _ ≤ -sSup (S e (u * r + (1 - u) * q)) := by
        rw [EReal.coe_neg, EReal.neg_le_neg_iff]; exact hm

lemma at_end (e : ℝ → ℝ) : hoeffdingTransform e (-e 1) = (e 1 : EReal) - leftSlope 0 e 1 := by
  set L := leftSlope 0 e 1 with hL
  have hT : L = sSup {v | ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ v = (((e 1 - e t) / (1 - t) : ℝ) : EReal)} := rfl
  have hel : ∀ s : ℝ, s < 1 → G e (-e 1) s = (e 1 - e s) / (1 - s) - e 1 := by
    intro s hs
    unfold G
    have : (1 - s) ≠ 0 := by linarith
    field_simp
    ring
  have hLb : L ≠ ⊥ := by
    apply ne_bot_of_le_ne_bot (EReal.coe_ne_bot ((e 1 - e 0) / (1 - 0)))
    rw [hT]; exact le_sSup ⟨0, le_rfl, one_pos, rfl⟩
  have key : sSup (S e (-e 1)) = L - (e 1 : EReal) := by
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨s, hs0, hs1, rfl⟩
      rw [hel s hs1, EReal.coe_sub]
      apply EReal.sub_le_sub _ le_rfl
      rw [hT]; exact le_sSup ⟨s, hs0, hs1, rfl⟩
    · rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)), hT]
      apply sSup_le
      rintro _ ⟨t, ht0, ht1, rfl⟩
      have : (((e 1 - e t) / (1 - t) : ℝ) : EReal) = ((G e (-e 1) t : ℝ) : EReal) + (e 1 : EReal) := by
        rw [← EReal.coe_add, hel t ht1]; congr 1; ring
      rw [this]
      exact add_le_add (le_sSup (show ((G e (-e 1) t : ℝ) : EReal) ∈ S e (-e 1) from
        ⟨t, ht0, ht1, rfl⟩)) le_rfl
  rw [psi_eq, key, EReal.neg_sub (Or.inl hLb) (Or.inr (EReal.coe_ne_top _)), add_comm,
    sub_eq_add_neg]

lemma usc (e : ℝ → ℝ) : UpperSemicontinuous (hoeffdingTransform e) := by
  intro x y hxy
  rw [psi_eq, EReal.neg_lt_comm, lt_sSup_iff] at hxy
  obtain ⟨_, ⟨s, hs0, hs1, rfl⟩, hlt⟩ := hxy
  have hc : Continuous (fun r : ℝ => ((G e r s : ℝ) : EReal)) := by
    apply continuous_coe_real_ereal.comp
    unfold G
    fun_prop
  filter_upwards [hc.continuousAt.eventually (lt_mem_nhds hlt)] with x' hx'
  rw [psi_eq, EReal.neg_lt_comm]
  exact lt_of_lt_of_le hx' (le_sSup ⟨s, hs0, hs1, rfl⟩)

lemma cont (e : ℝ → ℝ) (hcont : ContinuousOn e (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (hoeffdingTransform e) (Set.Ioi (-e 1)) := by
  set φ : ℝ → ℝ := fun r => (hoeffdingTransform e r).toReal
  have hφ : ∀ r ∈ Set.Ioi (-e 1), hoeffdingTransform e r = (φ r : EReal) :=
    fun r hr => finite e hcont hr
  have hconc : ConcaveOn ℝ (Set.Ioi (-e 1)) φ := by
    refine ⟨convex_Ioi _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    have hm : a • x + (1 - a) • y ∈ Set.Ioi (-e 1) := (convex_Ioi _) hx hy ha hb hab
    have := concave e x y a ha (by linarith)
    rw [hφ x hx, hφ y hy, ← smul_eq_mul a x, ← smul_eq_mul (1 - a) y, hφ _ hm,
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
    simpa [smul_eq_mul] using this
  have := hconc.continuousOn_interior
  rw [interior_Ioi] at this
  exact (continuous_coe_real_ereal.comp_continuousOn this).congr hφ

end G59H

theorem solution (e : ℝ → ℝ)
    (hcont : ContinuousOn e (Set.Icc (0 : ℝ) 1))
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) e) :
    (∀ r : ℝ, hoeffdingTransform e r =
      -sSup {v | ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ v = (((-s * r - e s) / (1 - s) : ℝ) : EReal)}) ∧
    (∀ r q u : ℝ, 0 ≤ u → u ≤ 1 →
      (u : EReal) * hoeffdingTransform e r + ((1 - u : ℝ) : EReal) * hoeffdingTransform e q ≤
        hoeffdingTransform e (u * r + (1 - u) * q)) ∧
    Monotone (hoeffdingTransform e) ∧
    (∀ r : ℝ, -e 1 < r → ∃ v : ℝ, hoeffdingTransform e r = (v : EReal)) ∧
    hoeffdingTransform e (-e 1) = (e 1 : EReal) - leftSlope 0 e 1 ∧
    ContinuousOn (hoeffdingTransform e) (Set.Ioi (-e 1)) ∧
    UpperSemicontinuous (hoeffdingTransform e) :=
  ⟨fun r => rfl, fun r q u h0 h1 => G59H.concave e r q u h0 h1, G59H.mono e,
    fun r hr => ⟨_, G59H.finite e hcont hr⟩, G59H.at_end e, G59H.cont e hcont, G59H.usc e⟩

end
