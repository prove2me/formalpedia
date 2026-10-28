-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P15.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:12:36.386976+00:00
-- url     : https://prove2.me/submissions/248e8163-7fef-4ae6-99f2-3423d96319c0

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15
noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction Topology

namespace QAlgorithms.Papers.Independent.Claimed50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

theorem S200T21_cont (a b : ℝ) (e : ℝ → ℝ) (hcont : ContinuousOn e (Set.Icc a b)) (θ : ℝ) :
    ContinuousOn (fun s : ℝ => θ * s - e s) (Set.Icc a b) :=
  (continuousOn_const.mul continuousOn_id).sub hcont

theorem S200T21_bdd (a b : ℝ) (e : ℝ → ℝ) (hcont : ContinuousOn e (Set.Icc a b)) (θ : ℝ) :
    BddAbove ((fun s : ℝ => θ * s - e s) '' Set.Icc a b) :=
  (isCompact_Icc.image_of_continuousOn (S200T21_cont a b e hcont θ)).bddAbove

theorem S200T21_le (a b : ℝ) (e : ℝ → ℝ) (hcont : ContinuousOn e (Set.Icc a b)) (θ u : ℝ)
    (hu : u ∈ Set.Icc a b) : θ * u - e u ≤ legendre a b e θ :=
  le_csSup (S200T21_bdd a b e hcont θ) (Set.mem_image_of_mem _ hu)

theorem S200T21_attain (a b : ℝ) (hab : a < b) (e : ℝ → ℝ) (hcont : ContinuousOn e (Set.Icc a b))
    (θ : ℝ) : ∃ u ∈ Set.Icc a b, legendre a b e θ = θ * u - e u := by
  have h := (isCompact_Icc.image_of_continuousOn (S200T21_cont a b e hcont θ)).sSup_mem
    ((Set.nonempty_Icc.mpr hab.le).image _)
  obtain ⟨u, hu, h2⟩ := h
  exact ⟨u, hu, h2.symm⟩

theorem S200T21_lower (a b : ℝ) (e : ℝ → ℝ) (hcont : ContinuousOn e (Set.Icc a b)) :
    ∃ m : ℝ, ∀ u ∈ Set.Icc a b, m ≤ e u := by
  obtain ⟨m, hm⟩ := (isCompact_Icc.image_of_continuousOn hcont).bddBelow
  exact ⟨m, fun u hu => hm (Set.mem_image_of_mem _ hu)⟩

theorem S200T21_sub_eq (a b : ℝ) (e : ℝ → ℝ) (hcont : ContinuousOn e (Set.Icc a b)) (s θ : ℝ)
    (h : convexSubgradient a b e s θ) : legendre a b e θ = θ * s - e s := by
  apply le_antisymm
  · apply csSup_le ((Set.nonempty_of_mem h.1).image _)
    rintro v ⟨u, hu, rfl⟩
    have := h.2 u hu
    simp only
    nlinarith
  · exact S200T21_le a b e hcont θ s h.1

theorem S200T21_sub_of (a b : ℝ) (e : ℝ → ℝ) (hcont : ContinuousOn e (Set.Icc a b)) (s θ : ℝ)
    (hs : s ∈ Set.Icc a b) (h : legendre a b e θ ≤ θ * s - e s) : convexSubgradient a b e s θ := by
  refine ⟨hs, fun u hu => ?_⟩
  have := S200T21_le a b e hcont θ u hu
  nlinarith

theorem S200T21_strict (a b : ℝ) (hab : a < b) (e : ℝ → ℝ) (hcont : ContinuousOn e (Set.Icc a b))
    (s r θ : ℝ) (h : ∀ u ∈ Set.Icc a b, r + θ * (u - s) < e u) :
    r < θ * s - legendre a b e θ := by
  obtain ⟨u, hu, hL⟩ := S200T21_attain a b hab e hcont θ
  have := h u hu
  rw [hL]; nlinarith

theorem S200T21_interior (a b : ℝ) (e : ℝ → ℝ) (hconv : ConvexOn ℝ (Set.Icc a b) e) (s : ℝ)
    (has : a < s) (hsb : s < b) :
    ∃ θ : ℝ, ∀ u ∈ Set.Icc a b, e s + θ * (u - s) ≤ e u := by
  set T := (fun t => (e s - e t) / (s - t)) '' Set.Ico a s
  have hne : T.Nonempty := ⟨_, Set.mem_image_of_mem _ (show a ∈ Set.Ico a s from ⟨le_rfl, has⟩)⟩
  have hsl : ∀ t ∈ Set.Ico a s, ∀ p, s < p → p ≤ b →
      (e s - e t) / (s - t) ≤ (e p - e s) / (p - s) := by
    intro t ht p hp hpb
    exact hconv.slope_mono_adjacent ⟨ht.1, ht.2.le.trans hsb.le⟩ ⟨has.le.trans hp.le, hpb⟩ ht.2 hp
  have hbdd : BddAbove T := by
    refine ⟨(e b - e s) / (b - s), ?_⟩
    rintro v ⟨t, ht, rfl⟩
    exact hsl t ht b hsb le_rfl
  refine ⟨sSup T, fun u hu => ?_⟩
  rcases lt_trichotomy u s with hus | hus | hus
  · have h1 : (e s - e u) / (s - u) ≤ sSup T :=
      le_csSup hbdd (Set.mem_image_of_mem _ (show u ∈ Set.Ico a s from ⟨hu.1, hus⟩))
    rw [div_le_iff₀ (by linarith)] at h1
    nlinarith
  · subst hus; simp
  · have h1 : sSup T ≤ (e u - e s) / (u - s) := by
      apply csSup_le hne
      rintro v ⟨t, ht, rfl⟩
      exact hsl t ht u hus hu.2
    rw [le_div_iff₀ (by linarith)] at h1
    nlinarith

/-- key: values θ s - L θ approach e s from below. -/
theorem S200T21_K (a b : ℝ) (hab : a < b) (e : ℝ → ℝ) (hcont : ContinuousOn e (Set.Icc a b))
    (hconv : ConvexOn ℝ (Set.Icc a b) e) (s r : ℝ) (hs : s ∈ Set.Icc a b) (hr : r < e s) :
    ∃ θ : ℝ, r < θ * s - legendre a b e θ := by
  obtain ⟨m, hm⟩ := S200T21_lower a b e hcont
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.mp (hcont s hs) (e s - r) (by linarith)
  have hnear : ∀ u ∈ Set.Icc a b, |u - s| < δ → r < e u := by
    intro u hu hd
    have := hδc hu (by rw [Real.dist_eq]; exact hd)
    rw [Real.dist_eq, abs_sub_lt_iff] at this
    linarith
  rcases eq_or_lt_of_le hs.1 with has | has
  · -- s = a
    refine ⟨-(|r - m| + 1) / δ, S200T21_strict a b hab e hcont s r _ ?_⟩
    intro u hu
    have hθ : -(|r - m| + 1) / δ * δ = -(|r - m| + 1) := div_mul_cancel₀ _ hδ.ne'
    have hθn : -(|r - m| + 1) / δ ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith [abs_nonneg (r - m)]) hδ.le
    by_cases hd : |u - s| < δ
    · have := hnear u hu hd
      have : -(|r - m| + 1) / δ * (u - s) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hθn (by linarith [hu.1, has])
      linarith
    · rw [abs_of_nonneg (by linarith [hu.1, has])] at hd
      push Not at hd
      have h1 : -(|r - m| + 1) / δ * (u - s) ≤ -(|r - m| + 1) / δ * δ :=
        mul_le_mul_of_nonpos_left hd hθn
      have := hm u hu
      have := le_abs_self (r - m)
      linarith
  rcases eq_or_lt_of_le hs.2 with hsb | hsb
  · -- s = b
    refine ⟨(|r - m| + 1) / δ, S200T21_strict a b hab e hcont s r _ ?_⟩
    intro u hu
    have hθ : (|r - m| + 1) / δ * δ = (|r - m| + 1) := div_mul_cancel₀ _ hδ.ne'
    have hθn : 0 ≤ (|r - m| + 1) / δ :=
      div_nonneg (by linarith [abs_nonneg (r - m)]) hδ.le
    by_cases hd : |u - s| < δ
    · have := hnear u hu hd
      have : (|r - m| + 1) / δ * (u - s) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hθn (by linarith [hu.2, hsb])
      linarith
    · rw [abs_of_nonpos (by linarith [hu.2, hsb])] at hd
      push Not at hd
      have hd' : δ ≤ s - u := by linarith
      have h1 : (|r - m| + 1) / δ * δ ≤ (|r - m| + 1) / δ * (s - u) :=
        mul_le_mul_of_nonneg_left hd' hθn
      have := hm u hu
      have := le_abs_self (r - m)
      linarith
  · obtain ⟨θ, hθ⟩ := S200T21_interior a b e hconv s has hsb
    exact ⟨θ, S200T21_strict a b hab e hcont s r θ (fun u hu => by linarith [hθ u hu])⟩

/-- growth outside the domain. -/
theorem S200T21_G (a b : ℝ) (hab : a < b) (e : ℝ → ℝ) (hcont : ContinuousOn e (Set.Icc a b))
    (s C : ℝ) (hs : s ∉ Set.Icc a b) : ∃ θ : ℝ, C < θ * s - legendre a b e θ := by
  obtain ⟨m, hm⟩ := S200T21_lower a b e hcont
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
  rcases hs with hs | hs
  · refine ⟨-(|C - m| + 1) / (a - s), ?_⟩
    have hθ : -(|C - m| + 1) / (a - s) * (a - s) = -(|C - m| + 1) :=
      div_mul_cancel₀ _ (by linarith)
    have hθn : -(|C - m| + 1) / (a - s) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith [abs_nonneg (C - m)]) (by linarith)
    obtain ⟨u, hu, hL⟩ := S200T21_attain a b hab e hcont (-(|C - m| + 1) / (a - s))
    rw [hL]
    have h1 : -(|C - m| + 1) / (a - s) * (u - a) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hθn (by linarith [hu.1])
    have := hm u hu
    have := le_abs_self (C - m)
    nlinarith
  · refine ⟨(|C - m| + 1) / (s - b), ?_⟩
    have hθ : (|C - m| + 1) / (s - b) * (s - b) = (|C - m| + 1) :=
      div_mul_cancel₀ _ (by linarith)
    have hθn : 0 ≤ (|C - m| + 1) / (s - b) :=
      div_nonneg (by linarith [abs_nonneg (C - m)]) (by linarith)
    obtain ⟨u, hu, hL⟩ := S200T21_attain a b hab e hcont ((|C - m| + 1) / (s - b))
    rw [hL]
    have h1 : (|C - m| + 1) / (s - b) * (u - b) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hθn (by linarith [hu.2])
    have := hm u hu
    have := le_abs_self (C - m)
    nlinarith

theorem S200T21_c3 (a b : ℝ) (hab : a < b) (e : ℝ → ℝ) (hcont : ContinuousOn e (Set.Icc a b))
    (hconv : ConvexOn ℝ (Set.Icc a b) e) (s : ℝ) :
    extendedConvex a b e s =
      sSup {v | ∃ theta : ℝ, v = ((s * theta - legendre a b e theta : ℝ) : EReal)} := by
  have key : ∀ x : EReal, x ≤ extendedConvex a b e s →
      (∀ r : ℝ, (r : EReal) < x → ∃ θ : ℝ, r < θ * s - legendre a b e θ) →
      x ≤ sSup {v | ∃ theta : ℝ, v = ((s * theta - legendre a b e theta : ℝ) : EReal)} := by
    intro x _ hx
    apply le_of_forall_lt
    intro c hc
    induction c using EReal.rec with
    | bot =>
      exact lt_of_lt_of_le (EReal.bot_lt_coe _) (le_sSup ⟨0, rfl⟩)
    | coe r =>
      obtain ⟨θ, hθ⟩ := hx r hc
      exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (by rw [mul_comm s θ]; exact hθ)) (le_sSup ⟨θ, rfl⟩)
    | top => exact absurd hc (not_top_lt)
  by_cases hs : s ∈ Set.Icc a b
  · apply le_antisymm
    · apply key _ le_rfl
      intro r hr
      simp only [extendedConvex, hs, if_true, EReal.coe_lt_coe_iff] at hr
      exact S200T21_K a b hab e hcont hconv s r hs hr
    · apply sSup_le
      rintro v ⟨θ, rfl⟩
      simp only [extendedConvex, hs, if_true, EReal.coe_le_coe_iff]
      linarith [S200T21_le a b e hcont θ s hs, mul_comm s θ]
  · have h1 : extendedConvex a b e s = ⊤ := by simp [extendedConvex, hs]
    rw [h1]
    exact le_antisymm (key ⊤ (by rw [h1]) (fun r _ => S200T21_G a b hab e hcont s r hs)) le_top

theorem S200T21_c4 (a b : ℝ) (hab : a < b) (e : ℝ → ℝ) (hcont : ContinuousOn e (Set.Icc a b))
    (hconv : ConvexOn ℝ (Set.Icc a b) e) (s θ : ℝ) :
    convexSubgradient a b e s θ ↔ finiteSubgradient (legendre a b e) θ s := by
  constructor
  · intro h η
    have h1 := S200T21_sub_eq a b e hcont s θ h
    have h2 := S200T21_le a b e hcont η s h.1
    rw [h1]; nlinarith
  · intro h
    have hb : ∀ η, η * s - legendre a b e η ≤ θ * s - legendre a b e θ := by
      intro η; have := h η; nlinarith
    have hs : s ∈ Set.Icc a b := by
      by_contra hs
      obtain ⟨η, hη⟩ := S200T21_G a b hab e hcont s (θ * s - legendre a b e θ) hs
      linarith [hb η]
    apply S200T21_sub_of a b e hcont s θ hs
    by_contra hlt
    push Not at hlt
    obtain ⟨η, hη⟩ := S200T21_K a b hab e hcont hconv s (θ * s - legendre a b e θ) hs (by linarith)
    linarith [hb η]

theorem S200T21_left (a b : ℝ) (e : ℝ → ℝ) (hconv : ConvexOn ℝ (Set.Icc a b) e)
    (ha : a < 0) (θ u : ℝ) (hθ : (θ : EReal) ≤ leftSlope a e 0) (hu0 : 0 < u) (hub : u ≤ b) :
    θ * u ≤ e u - e 0 := by
  have h1 : leftSlope a e 0 ≤ (((e u - e 0) / (u - 0) : ℝ) : EReal) := by
    apply sSup_le
    rintro v ⟨t, hat, ht0, rfl⟩
    exact EReal.coe_le_coe_iff.mpr
      (hconv.slope_mono_adjacent ⟨hat, by linarith⟩ ⟨by linarith, hub⟩ ht0 hu0)
  have h2 := EReal.coe_le_coe_iff.mp (hθ.trans h1)
  rw [sub_zero, le_div_iff₀ hu0] at h2
  exact h2

theorem S200T21_right (a b : ℝ) (e : ℝ → ℝ) (hconv : ConvexOn ℝ (Set.Icc a b) e)
    (hb : 0 < b) (θ u : ℝ) (hθ : rightSlope b e 0 ≤ (θ : EReal)) (hu0 : u < 0) (hau : a ≤ u) :
    θ * u ≤ e u - e 0 := by
  have h1 : ((((e 0 - e u) / (0 - u)) : ℝ) : EReal) ≤ rightSlope b e 0 := by
    apply le_sInf
    rintro v ⟨t, h0t, htb, rfl⟩
    exact EReal.coe_le_coe_iff.mpr
      (hconv.slope_mono_adjacent ⟨hau, by linarith⟩ ⟨by linarith, htb⟩ hu0 h0t)
  have h2 := EReal.coe_le_coe_iff.mp (h1.trans hθ)
  rw [div_le_iff₀ (by linarith)] at h2
  nlinarith

theorem S200T21_c5 (a b : ℝ) (hab : a < b) (e : ℝ → ℝ) (hcont : ContinuousOn e (Set.Icc a b))
    (hconv : ConvexOn ℝ (Set.Icc a b) e) (ha : a < 0) (hb : 0 < b) :
      AntitoneOn (legendre a b e) {theta | (theta : EReal) ≤ leftSlope a e 0} ∧
      MonotoneOn (legendre a b e) {theta | rightSlope b e 0 ≤ (theta : EReal)} ∧
      (∀ theta : ℝ, convexSubgradient a b e 0 theta → legendre a b e theta = -e 0) ∧
      (∀ theta : ℝ, ¬convexSubgradient a b e 0 theta → -e 0 < legendre a b e theta) := by
  have h0 : (0 : ℝ) ∈ Set.Icc a b := ⟨ha.le, hb.le⟩
  have hL0 : ∀ θ, -e 0 ≤ legendre a b e θ := by
    intro θ; have := S200T21_le a b e hcont θ 0 h0; simpa using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ1 _ θ2 h2 h12
    obtain ⟨u, hu, hL⟩ := S200T21_attain a b hab e hcont θ2
    rw [hL]
    rcases le_or_gt u 0 with hu0 | hu0
    · have := S200T21_le a b e hcont θ1 u hu
      nlinarith
    · have := S200T21_left a b e hconv ha θ2 u h2 hu0 hu.2
      linarith [hL0 θ1]
  · intro θ1 h1 θ2 _ h12
    obtain ⟨u, hu, hL⟩ := S200T21_attain a b hab e hcont θ1
    rw [hL]
    rcases le_or_gt 0 u with hu0 | hu0
    · have := S200T21_le a b e hcont θ2 u hu
      nlinarith
    · have := S200T21_right a b e hconv hb θ1 u h1 hu0 hu.1
      linarith [hL0 θ2]
  · intro θ h
    rw [S200T21_sub_eq a b e hcont 0 θ h]; ring
  · intro θ h
    rcases lt_or_eq_of_le (hL0 θ) with h' | h'
    · exact h'
    · exact absurd (S200T21_sub_of a b e hcont 0 θ h0 (by rw [mul_zero, zero_sub]; exact h'.symm.le)) h

theorem S200T21_c3' (a b : ℝ) (hab : a < b) (e : ℝ → ℝ) (hcont : ContinuousOn e (Set.Icc a b))
    (hconv : ConvexOn ℝ (Set.Icc a b) e) (s : ℝ) :
    extendedConvex a b e s =
      sSup {v | ∃ theta : ℝ, v = ((s * theta - legendre a b e theta : ℝ) : EReal)} := by
  exact S200T21_c3 a b hab e hcont hconv s

theorem S200T21_c6a (a b : ℝ) (hab : a < b) (e : ℝ → ℝ) (hcont : ContinuousOn e (Set.Icc a b))
    (θ : ℝ) (hθ : (θ : EReal) ≤ rightSlope b e a) : legendre a b e θ = a * θ - e a := by
  have hk : ∀ t ∈ Set.Icc a b, θ * t - e t ≤ θ * a - e a := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h; exact le_rfl
    · have h1 : rightSlope b e a ≤ (((e t - e a) / (t - a) : ℝ) : EReal) :=
        sInf_le ⟨t, h, ht.2, rfl⟩
      have h2 := EReal.coe_le_coe_iff.mp (hθ.trans h1)
      rw [le_div_iff₀ (by linarith)] at h2
      nlinarith
  apply le_antisymm
  · apply csSup_le ((Set.nonempty_Icc.mpr hab.le).image _)
    rintro v ⟨u, hu, rfl⟩
    have := hk u hu; linarith
  · have := S200T21_le a b e hcont θ a ⟨le_rfl, hab.le⟩; linarith

theorem S200T21_c6b (a b : ℝ) (hab : a < b) (e : ℝ → ℝ) (hcont : ContinuousOn e (Set.Icc a b))
    (θ : ℝ) (hθ : leftSlope a e b ≤ (θ : EReal)) : legendre a b e θ = b * θ - e b := by
  have hk : ∀ t ∈ Set.Icc a b, θ * t - e t ≤ θ * b - e b := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · subst h; exact le_rfl
    · have h1 : (((e b - e t) / (b - t) : ℝ) : EReal) ≤ leftSlope a e b :=
        le_sSup ⟨t, ht.1, h, rfl⟩
      have h2 := EReal.coe_le_coe_iff.mp (h1.trans hθ)
      rw [div_le_iff₀ (by linarith)] at h2
      nlinarith
  apply le_antisymm
  · apply csSup_le ((Set.nonempty_Icc.mpr hab.le).image _)
    rintro v ⟨u, hu, rfl⟩
    have := hk u hu; linarith
  · have := S200T21_le a b e hcont θ b ⟨hab.le, le_rfl⟩; linarith

end QAlgorithms.Papers.Independent.Claimed50.P15

open QAlgorithms.Papers.Independent.Claimed50.P15 in
theorem solution (a b : ℝ) (hab : a < b) (e : ℝ → ℝ)
    (hcont : ContinuousOn e (Set.Icc a b)) (hconv : ConvexOn ℝ (Set.Icc a b) e) :
    (∀ s theta : ℝ, ((s * theta : ℝ) : EReal) ≤
      extendedConvex a b e s + (legendre a b e theta : EReal)) ∧
    (∀ s theta : ℝ, (((s * theta : ℝ) : EReal) =
      extendedConvex a b e s + (legendre a b e theta : EReal)) ↔
      convexSubgradient a b e s theta) ∧
    (∀ s theta : ℝ, convexSubgradient a b e s theta ↔
      finiteSubgradient (legendre a b e) theta s) ∧
    (∀ s : ℝ, extendedConvex a b e s =
      sSup {v | ∃ theta : ℝ, v = ((s * theta - legendre a b e theta : ℝ) : EReal)}) ∧
    (a < 0 ∧ 0 < b →
      AntitoneOn (legendre a b e) {theta | (theta : EReal) ≤ leftSlope a e 0} ∧
      MonotoneOn (legendre a b e) {theta | rightSlope b e 0 ≤ (theta : EReal)} ∧
      (∀ theta : ℝ, convexSubgradient a b e 0 theta → legendre a b e theta = -e 0) ∧
      (∀ theta : ℝ, ¬convexSubgradient a b e 0 theta → -e 0 < legendre a b e theta)) ∧
    ((∀ theta : ℝ, (theta : EReal) ≤ rightSlope b e a → legendre a b e theta = a * theta - e a) ∧
      (∀ theta : ℝ, leftSlope a e b ≤ (theta : EReal) → legendre a b e theta = b * theta - e b)) := by
  refine ⟨?_, ?_, S200T21_c4 a b hab e hcont hconv, S200T21_c3' a b hab e hcont hconv,
    fun h => S200T21_c5 a b hab e hcont hconv h.1 h.2,
    S200T21_c6a a b hab e hcont, S200T21_c6b a b hab e hcont⟩
  · intro s θ
    by_cases hs : s ∈ Set.Icc a b
    · simp only [extendedConvex, hs, if_true]
      rw [← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith [S200T21_le a b e hcont θ s hs, mul_comm s θ]
    · simp [extendedConvex, hs]
  · intro s θ
    by_cases hs : s ∈ Set.Icc a b
    · simp only [extendedConvex, hs, if_true]
      rw [← EReal.coe_add, EReal.coe_eq_coe_iff]
      constructor
      · intro h
        exact S200T21_sub_of a b e hcont s θ hs (by linarith [mul_comm s θ])
      · intro h
        have := S200T21_sub_eq a b e hcont s θ h
        linarith [mul_comm s θ]
    · simp only [extendedConvex, hs, if_false, EReal.top_add_coe]
      constructor
      · intro h; exact absurd h (EReal.coe_ne_top _)
      · intro h; exact absurd h.1 hs


end
