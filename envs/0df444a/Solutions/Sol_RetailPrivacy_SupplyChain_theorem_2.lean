-- Prove2me | solution 1 for RetailPrivacy.SupplyChain.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T05:46:30.031747+00:00
-- url     : https://prove2.me/submissions/f6468d7e-9c3d-43a3-b74f-fe94970c9fca

import Mathlib
import Definitions.Def_RetailPrivacy_SupplyChain_Model

set_option autoImplicit false

namespace RPSCH

/-- generic demand: clamp (x / a) to [0, 1] -/
noncomputable def gD (a x : ℝ) : ℝ := max 0 (min 1 (x / a))
/-- generic retailer profit at wholesale `w` and margin variable `x = v - p` -/
noncomputable def gG (a e v w x : ℝ) : ℝ := (v - w - x) * gD a x + e * (max 0 (min x a)) ^ 2
/-- generic retailer best response (in `x = v - p`) -/
noncomputable def gX (a k v w : ℝ) : ℝ := if v - w ≤ 0 then 0 else a * min 1 ((v - w) / (2 * k))
/-- equilibrium wholesale price -/
noncomputable def wS (k v : ℝ) : ℝ := if v ≤ 4 * k then v / 2 else v - 2 * k
/-- equilibrium margin -/
noncomputable def xS (a k v : ℝ) : ℝ := if v ≤ 4 * k then a * (v / (4 * k)) else a
noncomputable def retS (k v : ℝ) : ℝ := if v ≤ 4 * k then v ^ 2 / (16 * k) else k
noncomputable def supS (k v : ℝ) : ℝ := if v ≤ 4 * k then v ^ 2 / (8 * k) else v - 2 * k

lemma gD_nonpos {a x : ℝ} (ha : 0 < a) (hx : x ≤ 0) : gD a x = 0 := by
  unfold gD
  have : x / a ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx ha.le
  exact max_eq_left (le_trans (min_le_right _ _) this)

lemma gD_mid {a x : ℝ} (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) : gD a x = x / a := by
  unfold gD
  have h1 : x / a ≤ 1 := (div_le_one ha).mpr hxa
  have h0 : 0 ≤ x / a := div_nonneg hx0 ha.le
  rw [min_eq_right h1, max_eq_right h0]

lemma gD_ge {a x : ℝ} (ha : 0 < a) (hxa : a ≤ x) : gD a x = 1 := by
  unfold gD
  have h1 : 1 ≤ x / a := (le_div_iff₀ ha).mpr (by linarith)
  rw [min_eq_left h1, max_eq_right zero_le_one]

lemma gG_nonpos {a e v w x : ℝ} (ha : 0 < a) (hx : x ≤ 0) : gG a e v w x = 0 := by
  unfold gG
  rw [gD_nonpos ha hx]
  have : min x a ≤ 0 := le_trans (min_le_left _ _) hx
  rw [max_eq_left this]; ring

/-- on [0, a], with `x = a * t` -/
lemma gG_mid {a e v w k t : ℝ} (ha : 0 < a) (hk : k = a - e * a ^ 2) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    gG a e v w (a * t) = (v - w) * t - k * t ^ 2 := by
  unfold gG
  have hx0 : 0 ≤ a * t := mul_nonneg ha.le ht0
  have hxa : a * t ≤ a := by nlinarith
  rw [gD_mid ha hx0 hxa, min_eq_left hxa, max_eq_right hx0]
  field_simp
  rw [hk]; ring

lemma gG_ge {a e v w x : ℝ} (ha : 0 < a) (hxa : a ≤ x) :
    gG a e v w x = (v - w - x) + e * a ^ 2 := by
  unfold gG
  rw [gD_ge ha hxa, min_eq_right hxa, max_eq_right ha.le]; ring

lemma gX_eq {a k v w : ℝ} (hu : 0 < v - w) : gX a k v w = a * min 1 ((v - w) / (2 * k)) := by
  unfold gX; rw [if_neg (by linarith)]

lemma gX_nonpos {a k v w : ℝ} (hu : v - w ≤ 0) : gX a k v w = 0 := by
  unfold gX; rw [if_pos hu]

/-- value of the best response -/
lemma gG_gX_pos {a e v w k : ℝ} (ha : 0 < a) (hk : k = a - e * a ^ 2) (hk0 : 0 < k)
    (hu : 0 < v - w) : 0 < gG a e v w (gX a k v w) := by
  rw [gX_eq hu]
  set t0 := min 1 ((v - w) / (2 * k)) with ht0
  have h1 : t0 ≤ 1 := min_le_left _ _
  have h2 : t0 ≤ (v - w) / (2 * k) := min_le_right _ _
  have h3 : 0 < t0 := lt_min one_pos (div_pos hu (by linarith))
  rw [gG_mid ha hk h3.le h1]
  have h4 : 2 * k * t0 ≤ v - w := by
    have := (le_div_iff₀ (by linarith : (0:ℝ) < 2 * k)).mp h2; linarith
  nlinarith

/-- quadratic comparison on [0,1] -/
lemma quad_le {u k t : ℝ} (hk0 : 0 < k) (hu : 0 < u) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    u * t - k * t ^ 2 ≤ u * min 1 (u / (2 * k)) - k * (min 1 (u / (2 * k))) ^ 2 ∧
    (u * min 1 (u / (2 * k)) - k * (min 1 (u / (2 * k))) ^ 2 ≤ u * t - k * t ^ 2 →
      t = min 1 (u / (2 * k))) := by
  rcases le_total 1 (u / (2 * k)) with h | h
  · rw [min_eq_left h]
    have h2k : 2 * k ≤ u := by
      have := (le_div_iff₀ (by linarith : (0:ℝ) < 2 * k)).mp h; linarith
    have h3 : 0 ≤ u - k * (1 + t) := by nlinarith
    refine ⟨by nlinarith [mul_nonneg (sub_nonneg.2 ht1) h3], fun hle => ?_⟩
    by_contra hne
    have hlt : t < 1 := lt_of_le_of_ne ht1 hne
    have h4 : 0 < u - k * (1 + t) := by nlinarith
    nlinarith [mul_pos (sub_pos.2 hlt) h4]
  · rw [min_eq_right h]
    have e1 : u / (2 * k) * (2 * k) = u := by field_simp
    refine ⟨by nlinarith [sq_nonneg (t - u / (2 * k))], fun hle => ?_⟩
    have : k * (t - u / (2 * k)) ^ 2 ≤ 0 := by nlinarith
    have : (t - u / (2 * k)) ^ 2 = 0 := le_antisymm (by
      by_contra hc; push Not at hc; nlinarith) (sq_nonneg _)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith

lemma gG_max {a e v w k : ℝ} (ha : 0 < a) (he : 0 ≤ e) (hk : k = a - e * a ^ 2) (hk0 : 0 < k)
    (x : ℝ) : gG a e v w x ≤ gG a e v w (gX a k v w) := by
  -- value of the middle piece
  have mid : ∀ t, 0 ≤ t → t ≤ 1 → gG a e v w (a * t) ≤ gG a e v w (gX a k v w) := by
    intro t ht0 ht1
    rw [gG_mid ha hk ht0 ht1]
    by_cases hu : v - w ≤ 0
    · rw [gX_nonpos hu, gG_nonpos ha le_rfl]; nlinarith
    · push Not at hu
      rw [gX_eq hu, gG_mid ha hk (le_min zero_le_one (div_pos hu (by linarith)).le) (min_le_left _ _)]
      exact (quad_le hk0 hu ht0 ht1).1
  rcases le_or_gt x 0 with hx | hx
  · rw [gG_nonpos ha hx]
    have := mid 0 le_rfl zero_le_one
    rw [mul_zero, gG_nonpos ha le_rfl] at this; exact this
  rcases le_or_gt x a with hxa | hxa
  · have := mid (x / a) (div_nonneg hx.le ha.le) ((div_le_one ha).mpr hxa)
    rwa [mul_div_cancel₀ x ha.ne'] at this
  · have h1 := mid 1 zero_le_one le_rfl
    rw [mul_one, gG_ge ha le_rfl] at h1
    rw [gG_ge ha hxa.le]; linarith

lemma gG_argmax_pos {a e v w k x : ℝ} (ha : 0 < a) (he : 0 ≤ e) (hk : k = a - e * a ^ 2)
    (hk0 : 0 < k) (hu : 0 < v - w) (hx : gG a e v w (gX a k v w) ≤ gG a e v w x) :
    x = gX a k v w := by
  have hpos := gG_gX_pos (e := e) ha hk hk0 hu
  rcases le_or_gt x 0 with hx0 | hx0
  · rw [gG_nonpos ha hx0] at hx; linarith
  rcases le_or_gt x a with hxa | hxa
  · have ht0 : 0 ≤ x / a := div_nonneg hx0.le ha.le
    have ht1 : x / a ≤ 1 := (div_le_one ha).mpr hxa
    have hxe : x = a * (x / a) := by field_simp
    rw [hxe, gG_mid ha hk ht0 ht1, gX_eq hu,
      gG_mid ha hk (le_min zero_le_one (div_pos hu (by linarith)).le) (min_le_left _ _)] at hx
    have := (quad_le hk0 hu ht0 ht1).2 hx
    rw [gX_eq hu, hxe, this]
  · exfalso
    have h1 := gG_max (v := v) (w := w) ha he hk hk0 a
    rw [gG_ge ha le_rfl] at h1
    rw [gG_ge ha hxa.le] at hx
    linarith

lemma gG_argmax_nonpos {a e v w k x : ℝ} (ha : 0 < a) (he : 0 ≤ e) (hk : k = a - e * a ^ 2)
    (hk0 : 0 < k) (hu : v - w ≤ 0) (hx : gG a e v w (gX a k v w) ≤ gG a e v w x) : x ≤ 0 := by
  rw [gX_nonpos hu, gG_nonpos ha le_rfl] at hx
  by_contra hx0; push Not at hx0
  rcases le_or_gt x a with hxa | hxa
  · have ht0 : 0 < x / a := div_pos hx0 ha
    have ht1 : x / a ≤ 1 := (div_le_one ha).mpr hxa
    have hxe : x = a * (x / a) := by field_simp
    rw [hxe, gG_mid ha hk ht0.le ht1] at hx
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hu ht0.le, mul_pos hk0 (pow_pos ht0 2)]
  · rw [gG_ge ha hxa.le] at hx
    have : e * a ^ 2 = a - k := by linarith
    linarith

lemma gD_gX {a k v w : ℝ} (ha : 0 < a) (hk0 : 0 < k) :
    gD a (gX a k v w) = if v - w ≤ 0 then 0 else min 1 ((v - w) / (2 * k)) := by
  by_cases hu : v - w ≤ 0
  · rw [gX_nonpos hu, if_pos hu, gD_nonpos ha le_rfl]
  · push Not at hu
    rw [gX_eq hu, if_neg (by linarith)]
    have h0 : 0 ≤ min 1 ((v - w) / (2 * k)) := le_min zero_le_one (div_pos hu (by linarith)).le
    have h1 : min 1 ((v - w) / (2 * k)) ≤ 1 := min_le_left _ _
    rw [gD_mid ha (mul_nonneg ha.le h0) (by nlinarith)]
    field_simp

/-- the supplier's objective against the best response -/
noncomputable def gPhi (a k v w : ℝ) : ℝ := w * gD a (gX a k v w)

lemma supS_pos {k v : ℝ} (hk0 : 0 < k) (hv : 0 < v) : 0 < supS k v := by
  unfold supS; split_ifs with h
  · positivity
  · push Not at h; linarith

lemma gPhi_wS {a k v : ℝ} (ha : 0 < a) (hk0 : 0 < k) (hv : 0 < v) :
    gPhi a k v (wS k v) = supS k v := by
  unfold gPhi; rw [gD_gX ha hk0]; unfold wS supS
  split_ifs with h1 h2 h2
  · linarith
  · rw [min_eq_right]
    · field_simp; ring
    · rw [div_le_one (by linarith)]; linarith
  · push Not at h1; linarith
  · rw [min_eq_left]; · ring
    rw [le_div_iff₀ (by linarith)]; linarith

lemma gPhi_le {a k v : ℝ} (ha : 0 < a) (hk0 : 0 < k) (hv : 0 < v) (w : ℝ) :
    gPhi a k v w ≤ supS k v ∧ (supS k v ≤ gPhi a k v w → w = wS k v) := by
  have hS := supS_pos hk0 hv
  unfold gPhi; rw [gD_gX ha hk0]
  by_cases hu : v - w ≤ 0
  · rw [if_pos hu]; simp only [mul_zero]
    exact ⟨hS.le, fun h => absurd h (not_le.mpr hS)⟩
  rw [if_neg hu]; push Not at hu
  rcases le_or_gt w 0 with hw | hw
  · have : w * min 1 ((v - w) / (2 * k)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hw (le_min zero_le_one (div_pos hu (by linarith)).le)
    exact ⟨by linarith, fun h => absurd h (by linarith)⟩
  have hm1 : min 1 ((v - w) / (2 * k)) ≤ (v - w) / (2 * k) := min_le_right _ _
  have hm2 : min 1 ((v - w) / (2 * k)) ≤ 1 := min_le_left _ _
  have e1 : (v - w) / (2 * k) * (2 * k) = v - w := by field_simp
  unfold supS wS
  split_ifs with h4
  · -- interior: w * min ≤ w (v-w)/(2k) ≤ v^2/(8k)
    have hA : w * min 1 ((v - w) / (2 * k)) ≤ w * ((v - w) / (2 * k)) :=
      mul_le_mul_of_nonneg_left hm1 hw.le
    have hB : w * ((v - w) / (2 * k)) = v ^ 2 / (8 * k) - (v - 2 * w) ^ 2 / (8 * k) := by
      field_simp; ring
    have hC : 0 ≤ (v - 2 * w) ^ 2 / (8 * k) := by positivity
    refine ⟨by linarith, fun h => ?_⟩
    have : (v - 2 * w) ^ 2 / (8 * k) ≤ 0 := by linarith
    have h0 : (v - 2 * w) ^ 2 = 0 := by
      have := (div_nonpos_iff.mp this)
      rcases this with ⟨_, h⟩ | ⟨h, _⟩
      · linarith
      · exact le_antisymm (by nlinarith) (sq_nonneg _)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
    linarith
  · push Not at h4
    rcases le_total w (v - 2 * k) with hw2 | hw2
    · have : 1 ≤ (v - w) / (2 * k) := by rw [le_div_iff₀ (by linarith)]; linarith
      rw [min_eq_left this, mul_one]
      exact ⟨hw2, fun h => le_antisymm hw2 h⟩
    · have hlt : (v - w) / (2 * k) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      rw [min_eq_right hlt]
      have key : w * ((v - w) / (2 * k)) = (v - 2 * k) - (w - (v - 2 * k)) * (w - 2 * k) / (2 * k) := by
        field_simp; ring
      have hpos : 0 ≤ (w - (v - 2 * k)) * (w - 2 * k) / (2 * k) := by
        apply div_nonneg _ (by linarith); apply mul_nonneg <;> linarith
      refine ⟨by linarith, fun h => ?_⟩
      have h0 : (w - (v - 2 * k)) * (w - 2 * k) / (2 * k) ≤ 0 := by linarith
      have h00 : (w - (v - 2 * k)) * (w - 2 * k) ≤ 0 := by
        have := mul_nonpos_of_nonpos_of_nonneg h0 (by linarith : (0:ℝ) ≤ 2 * k)
        rwa [div_mul_cancel₀ _ (by linarith : (2 * k : ℝ) ≠ 0)] at this
      have : w - 2 * k > 0 := by linarith
      nlinarith

/-- generic subgame: any best responses pin the outcome -/
theorem sub_spe {a e k v : ℝ} (ha : 0 < a) (he : 0 ≤ e) (hk : k = a - e * a ^ 2) (hk0 : 0 < k)
    (hv : 0 < v) (price : ℝ → ℝ) (w0 : ℝ)
    (hBR : ∀ w p', gG a e v w (v - p') ≤ gG a e v w (v - price w))
    (hS : ∀ w', w' * gD a (v - price w') ≤ w0 * gD a (v - price w0)) :
    w0 = wS k v ∧ v - price w0 = xS a k v := by
  have hDeq : ∀ w, gD a (v - price w) = gD a (gX a k v w) := by
    intro w
    have h := hBR w (v - gX a k v w)
    rw [sub_sub_cancel] at h
    by_cases hu : v - w ≤ 0
    · rw [gD_nonpos ha (gG_argmax_nonpos ha he hk hk0 hu h), gX_nonpos hu, gD_nonpos ha le_rfl]
    · push Not at hu; rw [gG_argmax_pos ha he hk hk0 hu h]
  have hS' : ∀ w', gPhi a k v w' ≤ gPhi a k v w0 := by
    intro w'; unfold gPhi; rw [← hDeq, ← hDeq]; exact hS w'
  have hw0 : w0 = wS k v := (gPhi_le ha hk0 hv w0).2 (by
    rw [← gPhi_wS ha hk0 hv]; exact hS' _)
  refine ⟨hw0, ?_⟩
  have hu : 0 < v - wS k v := by
    unfold wS; split_ifs with h
    · linarith
    · push Not at h; linarith
  have h := hBR w0 (v - gX a k v w0)
  rw [sub_sub_cancel] at h
  rw [gG_argmax_pos ha he hk hk0 (by rw [hw0]; exact hu) h, hw0, gX_eq hu]
  unfold xS wS
  split_ifs with h1
  · congr 1; rw [min_eq_right]
    · field_simp; ring
    · rw [div_le_one (by linarith)]; linarith
  · push Not at h1
    rw [min_eq_left, mul_one]
    rw [le_div_iff₀ (by linarith)]; linarith

lemma xS_mem {a k v : ℝ} (ha : 0 < a) (hk0 : 0 < k) (hv : 0 < v) :
    0 < xS a k v ∧ xS a k v ≤ a := by
  unfold xS; split_ifs with h
  · refine ⟨by positivity, ?_⟩
    have : v / (4 * k) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith
  · exact ⟨ha, le_rfl⟩

lemma gG_onpath {a e k v : ℝ} (ha : 0 < a) (hk : k = a - e * a ^ 2) (hk0 : 0 < k) (hv : 0 < v) :
    gG a e v (wS k v) (xS a k v) = retS k v ∧ wS k v * gD a (xS a k v) = supS k v := by
  unfold xS wS retS supS
  split_ifs with h
  · have ht1 : v / (4 * k) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    rw [gG_mid ha hk (by positivity) ht1, gD_mid ha (by positivity) (by nlinarith)]
    constructor <;> field_simp <;> ring
  · push Not at h
    have := gG_mid (e := e) (v := v) (w := v - 2 * k) ha hk zero_le_one le_rfl
    rw [mul_one] at this
    rw [this, gD_ge ha le_rfl]
    constructor <;> ring


open RetailPrivacy.SingleFirm MeasureTheory

lemma vol1 (B : ℝ) :
    (volume {θ : ℝ | θ ∈ Set.Icc (0:ℝ) 1 ∧ θ ≤ B}).toReal = max 0 (min 1 B) := by
  have : {θ : ℝ | θ ∈ Set.Icc (0:ℝ) 1 ∧ θ ≤ B} = Set.Icc 0 (min 1 B) := by
    ext θ; simp only [Set.mem_ofPred_eq, Set.mem_Icc, le_min_iff]; tauto
  rw [this, Real.volume_Icc, ENNReal.toReal_ofReal', sub_zero, max_comm]

lemma vol2 (A B : ℝ) :
    (volume {θ : ℝ | θ ∈ Set.Icc (0:ℝ) 1 ∧ A ≤ θ ∧ θ ≤ B}).toReal = max 0 (min 1 B - max 0 A) := by
  have : {θ : ℝ | θ ∈ Set.Icc (0:ℝ) 1 ∧ A ≤ θ ∧ θ ≤ B} = Set.Icc (max 0 A) (min 1 B) := by
    ext θ; simp only [Set.mem_ofPred_eq, Set.mem_Icc, le_min_iff, max_le_iff]; tauto
  rw [this, Real.volume_Icc, ENNReal.toReal_ofReal', max_comm]

lemma demand_false (v δ p r : ℝ) : demand false v δ p r = gD 1 (v - p) := by
  unfold demand gD
  have : {θ : ℝ | θ ∈ Set.Icc (0:ℝ) 1 ∧ 0 ≤ buyUtil false v δ p r θ} =
      {θ : ℝ | θ ∈ Set.Icc (0:ℝ) 1 ∧ θ ≤ v - p} := by
    ext θ
    simp only [Set.mem_ofPred_eq, buyUtil, utilHide, Bool.false_eq_true, ↓reduceIte]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
  rw [this, vol1, div_one]

lemma demand_true {v δ p r : ℝ} (hδ1 : δ < 1) :
    demand true v δ p r = max 0 (min 1 (max (v - p) ((v - p - r * δ) / (1 - δ)))) := by
  unfold demand
  have hp : (0:ℝ) < 1 - δ := by linarith
  have : {θ : ℝ | θ ∈ Set.Icc (0:ℝ) 1 ∧ 0 ≤ buyUtil true v δ p r θ} =
      {θ : ℝ | θ ∈ Set.Icc (0:ℝ) 1 ∧ θ ≤ max (v - p) ((v - p - r * δ) / (1 - δ))} := by
    ext θ
    simp only [Set.mem_ofPred_eq, buyUtil, utilHide, utilDisclose, ↓reduceIte, le_max_iff,
      le_div_iff₀ hp]
    constructor
    · rintro ⟨h1, h | h⟩
      · exact ⟨h1, Or.inl (by linarith)⟩
      · exact ⟨h1, Or.inr (by linarith)⟩
    · rintro ⟨h1, h | h⟩
      · exact ⟨h1, Or.inl (by linarith)⟩
      · exact ⟨h1, Or.inr (by linarith)⟩
  rw [this, vol1]

lemma disclose_eq {v δ p r : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    discloseQty v δ p r = max 0 (min 1 ((v - p - r * δ) / (1 - δ)) - max 0 r) := by
  unfold discloseQty
  have hp : (0:ℝ) < 1 - δ := by linarith
  have : {θ : ℝ | θ ∈ Set.Icc (0:ℝ) 1 ∧ utilHide v p θ ≤ utilDisclose v δ p r θ ∧
      0 ≤ utilDisclose v δ p r θ} =
      {θ : ℝ | θ ∈ Set.Icc (0:ℝ) 1 ∧ r ≤ θ ∧ θ ≤ (v - p - r * δ) / (1 - δ)} := by
    ext θ
    simp only [Set.mem_ofPred_eq, utilHide, utilDisclose, le_div_iff₀ hp]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, by linarith⟩
      have : r * δ ≤ θ * δ := by linarith
      exact le_of_mul_le_mul_right this hδ0
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, by linarith⟩
      nlinarith [mul_le_mul_of_nonneg_right h2 hδ0.le]
  rw [this, vol2]

/-! ### linear integrals and consumer surplus -/

lemma lin_int (A B α β : ℝ) :
    ∫ θ in α..β, (A - B * θ) = (A * β - B * β ^ 2 / 2) - (A * α - B * α ^ 2 / 2) := by
  have h : ∀ θ ∈ Set.uIcc α β,
      HasDerivAt (fun θ => A * θ - B * θ ^ 2 / 2) (A - B * θ) θ := by
    intro θ _
    have h1 : HasDerivAt (fun θ => A * θ - B * θ ^ 2 / 2) (A * 1 - B * (2 * θ ^ 1) / 2) θ := by
      apply HasDerivAt.sub
      · exact (hasDerivAt_id' θ).const_mul A
      · apply HasDerivAt.div_const; apply HasDerivAt.const_mul; simpa using hasDerivAt_pow 2 θ
    convert h1 using 1; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    (by apply Continuous.intervalIntegrable; fun_prop)]

lemma cs_false {v δ p r : ℝ} (hx0 : 0 ≤ v - p) (hx1 : v - p ≤ 1) :
    consumerSurplus false v δ p r = (v - p) ^ 2 / 2 := by
  unfold consumerSurplus
  set x := v - p with hxdef
  have hf : Continuous (fun θ : ℝ => max 0 (buyUtil false v δ p r θ)) := by
    simp only [buyUtil, utilHide, Bool.false_eq_true, ↓reduceIte]
    exact continuous_const.max (by fun_prop)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := x) (hf.intervalIntegrable 0 x)
    (hf.intervalIntegrable x 1)]
  have e1 : ∫ θ in (0:ℝ)..x, max 0 (buyUtil false v δ p r θ) = ∫ θ in (0:ℝ)..x, (x - 1 * θ) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le hx0] at hθ
    simp only [buyUtil, utilHide, Bool.false_eq_true, ↓reduceIte]
    rw [max_eq_right (by linarith [hθ.2])]; ring
  have e2 : ∫ θ in x..(1:ℝ), max 0 (buyUtil false v δ p r θ) = ∫ θ in x..(1:ℝ), ((0:ℝ) - 0 * θ) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le hx1] at hθ
    simp only [buyUtil, utilHide, Bool.false_eq_true, ↓reduceIte]
    rw [max_eq_left (by linarith [hθ.1])]; ring
  rw [e1, e2, lin_int, lin_int]; ring

/-- consumer surplus with collection, when `0 ≤ r ≤ x` and the disclosure cutoff is `≤ 1` -/
lemma cs_true {v δ p r : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 ≤ r) (hrx : r ≤ v - p)
    (hD1 : (v - p - r * δ) / (1 - δ) ≤ 1) :
    consumerSurplus true v δ p r =
      ((v - p) * r - r ^ 2 / 2) +
      ((v - p - r * δ) * ((v - p - r * δ) / (1 - δ) - r) -
        (1 - δ) * (((v - p - r * δ) / (1 - δ)) ^ 2 - r ^ 2) / 2) := by
  unfold consumerSurplus
  set x := v - p with hxdef
  set D := (x - r * δ) / (1 - δ) with hD
  have hp : (0:ℝ) < 1 - δ := by linarith
  have hDe : D * (1 - δ) = x - r * δ := by rw [hD]; field_simp
  have hrD : r ≤ D := by nlinarith
  have hxD : x ≤ D := by nlinarith
  have hf : Continuous (fun θ : ℝ => max 0 (buyUtil true v δ p r θ)) := by
    simp only [buyUtil, utilHide, utilDisclose, ↓reduceIte]
    exact continuous_const.max (Continuous.max (by fun_prop) (by fun_prop))
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := D) (hf.intervalIntegrable 0 D)
    (hf.intervalIntegrable D 1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := r) (hf.intervalIntegrable 0 r)
    (hf.intervalIntegrable r D)]
  have e1 : ∫ θ in (0:ℝ)..r, max 0 (buyUtil true v δ p r θ) = ∫ θ in (0:ℝ)..r, (x - 1 * θ) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le hr0] at hθ
    simp only [buyUtil, utilHide, utilDisclose, ↓reduceIte]
    have h1 : v - p - (1 - δ) * θ - r * δ ≤ v - p - θ := by nlinarith [hθ.2]
    rw [max_eq_left h1, max_eq_right (by linarith [hθ.2])]; ring
  have e2 : ∫ θ in r..D, max 0 (buyUtil true v δ p r θ) =
      ∫ θ in r..D, ((x - r * δ) - (1 - δ) * θ) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le hrD] at hθ
    simp only [buyUtil, utilHide, utilDisclose, ↓reduceIte]
    have h1 : v - p - θ ≤ v - p - (1 - δ) * θ - r * δ := by nlinarith [hθ.1]
    have h2 : 0 ≤ v - p - (1 - δ) * θ - r * δ := by nlinarith [hθ.2]
    rw [max_eq_right h1, max_eq_right h2]; ring
  have e3 : ∫ θ in D..(1:ℝ), max 0 (buyUtil true v δ p r θ) = ∫ θ in D..(1:ℝ), ((0:ℝ) - 0 * θ) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le hD1] at hθ
    simp only [buyUtil, utilHide, utilDisclose, ↓reduceIte]
    have h1 : v - p - θ ≤ 0 := by linarith [hθ.1]
    have h2 : v - p - (1 - δ) * θ - r * δ ≤ 0 := by nlinarith [hθ.1]
    rw [max_eq_left (max_le h1 h2)]; ring
  rw [e1, e2, e3, lin_int, lin_int, lin_int]; ring

/-! ### the R-mode response with collection -/

noncomputable def Kc (c δ : ℝ) : ℝ := 2 * c * (1 - δ) + δ
noncomputable def aR (c δ : ℝ) : ℝ := Kc c δ / Zc c δ
noncomputable def yR (c δ x : ℝ) : ℝ := max 0 (min x (aR c δ))
noncomputable def sR (c δ x : ℝ) : ℝ := 2 * c * yR c δ x / Kc c δ
noncomputable def rR (c δ x : ℝ) : ℝ := δ * yR c δ x / Kc c δ

section RR
variable {c δ : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1)
include hc hδ0 hδ1

lemma Kc_pos : 0 < Kc c δ := by unfold Kc; nlinarith
lemma Zc_pos : 0 < Zc c δ := by unfold Zc; linarith
lemma aR_pos : 0 < aR c δ := div_pos (Kc_pos hc hδ0 hδ1) (Zc_pos hc hδ0 hδ1)
lemma K_id : Kc c δ - δ ^ 2 = (1 - δ) * Zc c δ := by unfold Kc Zc; ring
lemma aR_mul : aR c δ * Zc c δ = Kc c δ := by
  unfold aR; field_simp [(Zc_pos hc hδ0 hδ1).ne']

lemma yR_nonneg (x : ℝ) : 0 ≤ yR c δ x := le_max_left _ _

/-- the disclosure cutoff at the R response, for `0 ≤ x ≤ aR` -/
lemma rR_mid {x : ℝ} (hx0 : 0 ≤ x) (hxa : x ≤ aR c δ) :
    yR c δ x = x ∧ (x - rR c δ x * δ) / (1 - δ) = x * Zc c δ / Kc c δ := by
  have hy : yR c δ x = x := by unfold yR; rw [min_eq_left hxa, max_eq_right hx0]
  refine ⟨hy, ?_⟩
  have hK := Kc_pos hc hδ0 hδ1
  have hp : (1:ℝ) - δ ≠ 0 := by linarith
  unfold rR; rw [hy]
  rw [div_eq_div_iff hp hK.ne']
  have := K_id hc hδ0 hδ1
  field_simp
  nlinarith [this]

lemma rR_hi {x : ℝ} (hxa : aR c δ ≤ x) :
    yR c δ x = aR c δ ∧ rR c δ x = δ / Zc c δ ∧ sR c δ x = 2 * c / Zc c δ := by
  have hy : yR c δ x = aR c δ := by
    unfold yR; rw [min_eq_right hxa, max_eq_right (aR_pos hc hδ0 hδ1).le]
  have hK := Kc_pos hc hδ0 hδ1
  have hZ := Zc_pos hc hδ0 hδ1
  refine ⟨hy, ?_, ?_⟩
  · unfold rR; rw [hy]; unfold aR; field_simp
  · unfold sR; rw [hy]; unfold aR; field_simp

lemma rR_lo {x : ℝ} (hx : x ≤ 0) : yR c δ x = 0 ∧ rR c δ x = 0 ∧ sR c δ x = 0 := by
  have hy : yR c δ x = 0 := by unfold yR; exact max_eq_left (le_trans (min_le_left _ _) hx)
  unfold rR sR; rw [hy]; simp

/-- the R response is a fixed point of the disclosure map -/
lemma sR_fixed (x : ℝ) :
    max 0 (min 1 ((x - rR c δ x * δ) / (1 - δ)) - max 0 (rR c δ x)) = sR c δ x := by
  have hK := Kc_pos hc hδ0 hδ1
  have hZ := Zc_pos hc hδ0 hδ1
  have hp : (0:ℝ) < 1 - δ := by linarith
  rcases le_or_gt x 0 with hx | hx
  · obtain ⟨_, hr, hs⟩ := rR_lo hc hδ0 hδ1 hx
    rw [hr, hs, max_self, sub_zero, zero_mul, sub_zero]
    exact max_eq_left (le_trans (min_le_right _ _) (div_nonpos_of_nonpos_of_nonneg hx hp.le))
  rcases le_total x (aR c δ) with hxa | hxa
  · obtain ⟨hy, hD⟩ := rR_mid hc hδ0 hδ1 hx.le hxa
    rw [hD]
    have hD1 : x * Zc c δ / Kc c δ ≤ 1 := by
      rw [div_le_one hK, ← aR_mul hc hδ0 hδ1]; nlinarith
    have hr0 : 0 ≤ rR c δ x := by unfold rR; rw [hy]; positivity
    rw [min_eq_right hD1, max_eq_right hr0]
    have : x * Zc c δ / Kc c δ - rR c δ x = sR c δ x := by
      unfold rR sR; rw [hy]; unfold Zc; field_simp; ring
    rw [this]; exact max_eq_right (by unfold sR; rw [hy]; positivity)
  · obtain ⟨hy, hr, hs⟩ := rR_hi hc hδ0 hδ1 hxa
    rw [hr, hs]
    have h1 : 1 ≤ (x - δ / Zc c δ * δ) / (1 - δ) := by
      rw [le_div_iff₀ hp]
      have : aR c δ = 1 - δ + δ ^ 2 / Zc c δ := by
        unfold aR; field_simp; unfold Kc Zc; ring
      have e2 : δ / Zc c δ * δ = δ ^ 2 / Zc c δ := by ring
      linarith
    rw [min_eq_left h1, max_eq_right (div_pos hδ0 hZ).le]
    have : 1 - δ / Zc c δ = 2 * c / Zc c δ := by field_simp; unfold Zc; ring
    rw [this]; exact max_eq_right (by positivity)

/-- the disclosure map is antitone -/
lemma phi_anti {x s1 s2 : ℝ} (h0 : 0 ≤ s1) (h12 : s1 ≤ s2) :
    max 0 (min 1 ((x - δ * s2 / (2 * c) * δ) / (1 - δ)) - max 0 (δ * s2 / (2 * c))) ≤
    max 0 (min 1 ((x - δ * s1 / (2 * c) * δ) / (1 - δ)) - max 0 (δ * s1 / (2 * c))) := by
  have hp : (0:ℝ) < 1 - δ := by linarith
  have m1 : δ * s1 / (2 * c) ≤ δ * s2 / (2 * c) := by
    apply div_le_div_of_nonneg_right _ (by linarith); nlinarith
  apply max_le_max le_rfl
  apply sub_le_sub
  · apply min_le_min le_rfl
    apply div_le_div_of_nonneg_right _ hp.le
    nlinarith
  · exact max_le_max le_rfl m1

/-- uniqueness of the REE in R mode with collection -/
lemma ree_R_unique {v p s r : ℝ} (h : IsREE .R true v c δ p s r) :
    s = sR c δ (v - p) ∧ r = rR c δ (v - p) := by
  unfold IsREE at h
  simp only [↓reduceIte] at h
  obtain ⟨hmax, hs⟩ := h
  have hs0 : 0 ≤ s := by rw [hs]; unfold discloseQty; exact ENNReal.toReal_nonneg
  have hr : r = δ * s / (2 * c) := by
    have h1 := isMaxOn_iff.mp hmax (δ * s / (2 * c)) (by
      show (0:ℝ) ≤ δ * s / (2 * c); positivity)
    unfold dataProfit at h1
    have key : δ * s / (2 * c) * δ * s - c * (δ * s / (2 * c)) ^ 2 - (r * δ * s - c * r ^ 2) =
        c * (r - δ * s / (2 * c)) ^ 2 := by field_simp; ring
    have h2 : c * (r - δ * s / (2 * c)) ^ 2 ≤ 0 := by linarith
    have h3 : (r - δ * s / (2 * c)) ^ 2 = 0 :=
      le_antisymm (by
        by_contra hc'; push Not at hc'; nlinarith) (sq_nonneg _)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
    linarith
  rw [disclose_eq hδ0 hδ1, hr] at hs
  -- the candidate
  set x := v - p with hxdef
  have hK := Kc_pos hc hδ0 hδ1
  have hrs : rR c δ x = δ * sR c δ x / (2 * c) := by
    unfold rR sR; field_simp
  have hfix := sR_fixed hc hδ0 hδ1 x
  rw [hrs] at hfix
  have hsR0 : 0 ≤ sR c δ x := by unfold sR; have := yR_nonneg hc hδ0 hδ1 x; positivity
  have hss : s = sR c δ x := by
    rcases lt_trichotomy s (sR c δ x) with hlt | heq | hgt
    · have := phi_anti hc hδ0 hδ1 (x := x) hs0 hlt.le
      rw [← hs, hfix] at this; linarith
    · exact heq
    · have := phi_anti hc hδ0 hδ1 (x := x) hsR0 hgt.le
      rw [← hs, hfix] at this; linarith
  refine ⟨hss, ?_⟩
  rw [hr, hss, ← hrs]

lemma ree_R_exists (v p : ℝ) : IsREE .R true v c δ p (sR c δ (v - p)) (rR c δ (v - p)) := by
  unfold IsREE
  simp only [↓reduceIte]
  have hrs : rR c δ (v - p) = δ * sR c δ (v - p) / (2 * c) := by
    unfold rR sR; field_simp
  refine ⟨?_, ?_⟩
  · rw [isMaxOn_iff]
    intro r' _
    unfold dataProfit
    rw [hrs]
    have key : δ * sR c δ (v - p) / (2 * c) * δ * sR c δ (v - p) -
        c * (δ * sR c δ (v - p) / (2 * c)) ^ 2 - (r' * δ * sR c δ (v - p) - c * r' ^ 2) =
        c * (r' - δ * sR c δ (v - p) / (2 * c)) ^ 2 := by field_simp; ring
    have := mul_nonneg hc.le (sq_nonneg (r' - δ * sR c δ (v - p) / (2 * c)))
    linarith
  · rw [disclose_eq hδ0 hδ1]
    exact (sR_fixed hc hδ0 hδ1 (v - p)).symm

/-- demand, data profit and surplus at the R response -/
lemma demand_R (v p : ℝ) : demand true v δ p (rR c δ (v - p)) = gD (aR c δ) (v - p) := by
  rw [demand_true hδ1]
  have hK := Kc_pos hc hδ0 hδ1
  have hZ := Zc_pos hc hδ0 hδ1
  have ha := aR_pos hc hδ0 hδ1
  have hp : (0:ℝ) < 1 - δ := by linarith
  unfold gD
  set x := v - p
  rcases le_or_gt x 0 with hx | hx
  · obtain ⟨_, hr, _⟩ := rR_lo hc hδ0 hδ1 hx
    rw [hr, zero_mul, sub_zero]
    have h1 : max x (x / (1 - δ)) ≤ 0 :=
      max_le hx (div_nonpos_of_nonpos_of_nonneg hx hp.le)
    rw [max_eq_left (le_trans (min_le_right _ _) h1),
      max_eq_left (le_trans (min_le_right _ _) (div_nonpos_of_nonpos_of_nonneg hx ha.le))]
  rcases le_total x (aR c δ) with hxa | hxa
  · obtain ⟨_, hD⟩ := rR_mid hc hδ0 hδ1 hx.le hxa
    rw [hD]
    have : x / aR c δ = x * Zc c δ / Kc c δ := by unfold aR; field_simp
    rw [this]
    have hxx : x ≤ x * Zc c δ / Kc c δ := by
      rw [le_div_iff₀ hK]; unfold Zc Kc; nlinarith [mul_pos hx (mul_pos hc hδ0)]
    rw [max_eq_right hxx]
  · obtain ⟨_, hr, _⟩ := rR_hi hc hδ0 hδ1 hxa
    rw [hr]
    have h1 : 1 ≤ (x - δ / Zc c δ * δ) / (1 - δ) := by
      rw [le_div_iff₀ hp]
      have : aR c δ = 1 - δ + δ ^ 2 / Zc c δ := by
        unfold aR; field_simp; unfold Kc Zc; ring
      have e2 : δ / Zc c δ * δ = δ ^ 2 / Zc c δ := by ring
      linarith
    have h2 : 1 ≤ x / aR c δ := by rw [le_div_iff₀ ha]; linarith
    rw [min_eq_left (le_trans h1 (le_max_right _ _)), min_eq_left h2]

lemma data_R (v p : ℝ) :
    dataProfit c δ (sR c δ (v - p)) (rR c δ (v - p)) =
      c * δ ^ 2 / Kc c δ ^ 2 * (max 0 (min (v - p) (aR c δ))) ^ 2 := by
  unfold dataProfit sR rR yR
  have hK := Kc_pos hc hδ0 hδ1
  field_simp; ring

lemma cs_R {v p : ℝ} (hx0 : 0 < v - p) (hxa : v - p ≤ aR c δ) :
    consumerSurplus true v δ p (rR c δ (v - p)) =
      Fc c δ / Zc c δ ^ 2 * ((v - p) / aR c δ) ^ 2 / 2 := by
  obtain ⟨hy, hD⟩ := rR_mid hc hδ0 hδ1 hx0.le hxa
  have hK := Kc_pos hc hδ0 hδ1
  have hZ := Zc_pos hc hδ0 hδ1
  have hrv : rR c δ (v - p) = δ * (v - p) / Kc c δ := by unfold rR; rw [hy]
  have hr0 : 0 ≤ rR c δ (v - p) := by rw [hrv]; positivity
  have hrx : rR c δ (v - p) ≤ v - p := by
    rw [hrv, div_le_iff₀ hK]; unfold Kc; nlinarith [mul_pos hx0 (mul_pos hc (sub_pos.2 hδ1))]
  have hD1 : (v - p - rR c δ (v - p) * δ) / (1 - δ) ≤ 1 := by
    rw [hD, div_le_one hK, ← aR_mul hc hδ0 hδ1]; nlinarith
  rw [cs_true hδ0 hδ1 hr0 hrx hD1, hD, hrv]
  unfold aR
  have hp : (1:ℝ) - δ ≠ 0 := by linarith
  field_simp
  unfold Fc Kc Zc
  ring

end RR

/-! ### C mode with collection, and no collection -/

lemma demand_C {v δ p : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) : demand true v δ p 0 = gD (1 - δ) (v - p) := by
  rw [demand_true hδ1, zero_mul, sub_zero]
  unfold gD
  have hp : (0:ℝ) < 1 - δ := by linarith
  rcases le_or_gt (v - p) 0 with hx | hx
  · have h1 : max (v - p) ((v - p) / (1 - δ)) ≤ 0 :=
      max_le hx (div_nonpos_of_nonpos_of_nonneg hx hp.le)
    rw [max_eq_left (le_trans (min_le_right _ _) h1),
      max_eq_left (le_trans (min_le_right _ _) (div_nonpos_of_nonpos_of_nonneg hx hp.le))]
  · have : v - p ≤ (v - p) / (1 - δ) := by
      rw [le_div_iff₀ hp]; nlinarith [mul_pos hx hδ0]
    rw [max_eq_right this]

lemma cs_C {v δ p : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hx0 : 0 < v - p) (hxa : v - p ≤ 1 - δ) :
    consumerSurplus true v δ p 0 = (1 - δ) * ((v - p) / (1 - δ)) ^ 2 / 2 := by
  have hp : (0:ℝ) < 1 - δ := by linarith
  rw [cs_true hδ0 hδ1 le_rfl hx0.le (by rw [zero_mul, sub_zero, div_le_one hp]; exact hxa)]
  field_simp; ring

noncomputable def csS (ρ k v : ℝ) : ℝ := if v ≤ 4 * k then ρ * v ^ 2 / (32 * k ^ 2) else ρ / 2

section Alg
variable {κ kR ρR v : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hκρ : κ < ρR) (hρk : ρR < kR) (hk1 : kR < 1)
  (hk2 : kR ^ 2 < ρR) (hκρk : κ * ρR < kR ^ 2) (hv : 0 < v)
include hκ0 hκ1 hκρ hρk hk1 hk2 hκρk hv

lemma retS_one (h : v ^ 2 < 16) : retS 1 v = v ^ 2 / 16 ∧ supS 1 v = v ^ 2 / 8 ∧
    csS 1 1 v = v ^ 2 / 32 := by
  have : v ≤ 4 * 1 := by nlinarith
  unfold retS supS csS; rw [if_pos this, if_pos this, if_pos this]; norm_num

/-- R collects for `v² < 16 kR` -/
lemma R_collects (h : v ^ 2 < 16 * kR) : retS 1 v < retS kR v := by
  have hk0 : 0 < kR := by linarith
  rw [(retS_one hκ0 hκ1 hκρ hρk hk1 hk2 hκρk hv (by nlinarith)).1]
  unfold retS; split_ifs with h1
  · rw [div_lt_div_iff₀ (by norm_num) (by positivity)]; nlinarith [mul_pos (pow_pos hv 2) (sub_pos.2 hk1)]
  · linarith

lemma C_collects (h : v ^ 2 < 16 * κ) : retS 1 v < retS κ v := by
  rw [(retS_one hκ0 hκ1 hκρ hρk hk1 hk2 hκρk hv (by nlinarith)).1]
  unfold retS; split_ifs with h1
  · rw [div_lt_div_iff₀ (by norm_num) (by positivity)]; nlinarith [mul_pos (pow_pos hv 2) (sub_pos.2 hκ1)]
  · linarith

lemma C_declines (h : 16 * κ < v ^ 2) (h' : v ^ 2 < 16) : retS κ v < retS 1 v := by
  rw [(retS_one hκ0 hκ1 hκρ hρk hk1 hk2 hκρk hv h').1]
  unfold retS; split_ifs with h1
  · nlinarith
  · linarith

/-- supplier comparison `v²/(8k) < v - 2κ` for `4κ < v < 4k` -/
lemma sup_aux {k : ℝ} (hk : 0 < k) (h1 : 4 * κ < v) (h2 : v ≤ 4 * k) (hkk : κ < k) :
    v ^ 2 / (8 * k) < v - 2 * κ := by
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ v - 4 * κ) (by linarith : (0:ℝ) ≤ 4 * k - v)]

lemma claim1 (h1 : 16 * κ < v ^ 2) (h2 : v ^ 2 < 16 * ρR) :
    csS 1 1 v < csS ρR kR v ∧ retS 1 v < retS kR v ∧ supS 1 v < supS kR v := by
  have hk0 : 0 < kR := by linarith
  obtain ⟨e1, e2, e3⟩ := retS_one hκ0 hκ1 hκρ hρk hk1 hk2 hκρk hv (by nlinarith)
  rw [e1, e2, e3]
  unfold retS supS csS
  split_ifs with h
  · refine ⟨?_, ?_, ?_⟩
    · rw [div_lt_div_iff₀ (by norm_num) (by positivity)]; nlinarith [sq_nonneg v]
    · rw [div_lt_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    · rw [div_lt_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  · push Not at h
    have hv4 : v < 4 := by nlinarith
    refine ⟨by linarith, by linarith, ?_⟩
    nlinarith [mul_pos (by linarith : (0:ℝ) < v - 4 * kR) (by linarith : (0:ℝ) < 4 - v)]

lemma claim2 (h : v ^ 2 < 16 * κ * kR) :
    csS ρR kR v < csS κ κ v ∧ retS kR v < retS κ v ∧ supS kR v < supS κ v := by
  have hk0 : 0 < kR := by linarith
  have hvk : v ≤ 4 * kR := by nlinarith
  unfold retS supS csS
  rw [if_pos hvk, if_pos hvk, if_pos hvk]
  split_ifs with hc
  · refine ⟨?_, ?_, ?_⟩
    · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      have : 0 < v ^ 2 := by positivity
      nlinarith [mul_pos this (by nlinarith : (0:ℝ) < kR ^ 2 - κ * ρR), mul_pos this hκ0]
    · rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [sq_pos_of_pos hv]
    · rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [sq_pos_of_pos hv]
  · push Not at hc
    refine ⟨?_, ?_, ?_⟩
    · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      -- ρR v² · 2 < κ · 32 kR²  from v² < 16 κ kR and ρR < kR
      nlinarith [mul_lt_mul_of_pos_left h (by linarith : (0:ℝ) < ρR)]
    · rw [div_lt_iff₀ (by positivity)]; nlinarith
    · have hv4 : v < 4 * kR := by nlinarith
      exact sup_aux hκ0 hκ1 hκρ hρk hk1 hk2 hκρk hv hk0 hc hv4.le (by linarith)

lemma claim3 (h1 : 16 * κ * kR < v ^ 2) (h2 : v ^ 2 < 16 * κ * kR ^ 2 / ρR) :
    retS κ v < retS kR v ∧ csS ρR kR v < csS κ κ v ∧ supS kR v < supS κ v := by
  have hk0 : 0 < kR := by linarith
  have hρ0 : 0 < ρR := by linarith
  have h2' : v ^ 2 * ρR < 16 * κ * kR ^ 2 := by rwa [lt_div_iff₀ hρ0] at h2
  have hvk : v < 4 * kR := by
    by_contra hc; push Not at hc
    have hh : (4 * kR) ^ 2 ≤ v ^ 2 := by nlinarith [mul_le_mul hc hc (by positivity) hv.le]
    nlinarith [mul_le_mul_of_nonneg_left hh hρ0.le, mul_lt_mul_of_pos_right hκρ (by positivity : (0:ℝ) < 16 * kR ^ 2)]
  have hvc : 4 * κ < v := by
    by_contra hc; push Not at hc
    have hh : v ^ 2 ≤ (4 * κ) ^ 2 := by nlinarith [mul_le_mul hc hc hv.le (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left (show κ < kR by linarith) (by positivity : (0:ℝ) < 16 * κ)]
  unfold retS supS csS
  rw [if_pos hvk.le, if_pos hvk.le, if_pos hvk.le, if_neg (by linarith), if_neg (by linarith),
    if_neg (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  · exact sup_aux hκ0 hκ1 hκρ hρk hk1 hk2 hκρk hv hk0 hvc hvk.le (by linarith)

lemma claim4 (h1 : 16 * κ * kR ^ 2 / ρR < v ^ 2) (h2 : v ^ 2 < 16 * κ) :
    retS κ v < retS kR v ∧ csS κ κ v < csS ρR kR v ∧ supS kR v < supS κ v := by
  have hk0 : 0 < kR := by linarith
  have hρ0 : 0 < ρR := by linarith
  have h1' : 16 * κ * kR ^ 2 < v ^ 2 * ρR := by rwa [div_lt_iff₀ hρ0] at h1
  have hvc : 4 * κ < v := by
    by_contra hc; push Not at hc
    have hh : v ^ 2 ≤ (4 * κ) ^ 2 := by nlinarith [mul_le_mul hc hc hv.le (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hh hρ0.le, mul_lt_mul_of_pos_left hκρk (by positivity : (0:ℝ) < 16 * κ)]
  unfold retS supS csS
  rw [if_neg (show ¬ v ≤ 4 * κ by linarith), if_neg (show ¬ v ≤ 4 * κ by linarith),
    if_neg (show ¬ v ≤ 4 * κ by linarith)]
  split_ifs with hk
  · refine ⟨?_, ?_, ?_⟩
    · rw [lt_div_iff₀ (by positivity)]; nlinarith
    · rw [div_lt_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    · exact sup_aux hκ0 hκ1 hκρ hρk hk1 hk2 hκρk hv hk0 hvc hk (by linarith)
  · refine ⟨by linarith, by linarith, by linarith⟩

lemma claim5 (h1 : 16 * ρR < v ^ 2) (h2 : v ^ 2 < 16 * kR) :
    csS ρR kR v < csS 1 1 v ∧ retS 1 v < retS kR v ∧ supS 1 v < supS kR v := by
  have hk0 : 0 < kR := by linarith
  obtain ⟨e1, e2, e3⟩ := retS_one hκ0 hκ1 hκρ hρk hk1 hk2 hκρk hv (by nlinarith)
  rw [e1, e2, e3]
  have hvk : 4 * kR < v := by nlinarith
  have hv4 : v < 4 := by nlinarith
  unfold retS supS csS
  rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
  refine ⟨by linarith, by linarith, ?_⟩
  nlinarith [mul_pos (by linarith : (0:ℝ) < v - 4 * kR) (by linarith : (0:ℝ) < 4 - v)]

end Alg


/-! ### assembly: on-path values in any SPE, and existence -/

theorem onpath_gen {a e k ρ v : ℝ} (ha : 0 < a) (he : 0 ≤ e) (hk : k = a - e * a ^ 2)
    (hk0 : 0 < k) (hv : 0 < v)
    (RP : ℝ → ℝ → ℝ) (SP : ℝ → ℝ → ℝ) (CSf : ℝ → ℝ) (price : ℝ → ℝ) (w0 : ℝ)
    (hRP : ∀ w p, RP w p = gG a e v w (v - p)) (hSP : ∀ w p, SP w p = w * gD a (v - p))
    (hCS : ∀ p, 0 < v - p → v - p ≤ a → CSf p = ρ * ((v - p) / a) ^ 2 / 2)
    (hBR : ∀ w p', RP w p' ≤ RP w (price w)) (hS : ∀ w', SP w' (price w') ≤ SP w0 (price w0)) :
    RP w0 (price w0) = retS k v ∧ SP w0 (price w0) = supS k v ∧ CSf (price w0) = csS ρ k v := by
  obtain ⟨hw, hx⟩ := sub_spe ha he hk hk0 hv price w0
    (fun w p' => by have := hBR w p'; rwa [hRP, hRP] at this)
    (fun w' => by have := hS w'; rwa [hSP, hSP] at this)
  obtain ⟨h1, h2⟩ := gG_onpath (e := e) ha hk hk0 hv
  obtain ⟨hx0, hxa⟩ := xS_mem ha hk0 hv
  refine ⟨by rw [hRP, hx, hw, h1], by rw [hSP, hx, hw, h2], ?_⟩
  rw [hCS _ (by rw [hx]; exact hx0) (by rw [hx]; exact hxa), hx]
  unfold xS csS
  split_ifs with h
  · field_simp; ring
  · rw [div_self ha.ne']; ring

noncomputable def kRv (c δ : ℝ) : ℝ := Mc c δ / Zc c δ ^ 2

lemma kRv_eq {c δ : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    kRv c δ = aR c δ - c * δ ^ 2 / Kc c δ ^ 2 * aR c δ ^ 2 := by
  have hK := Kc_pos hc hδ0 hδ1
  have hZ := Zc_pos hc hδ0 hδ1
  unfold kRv aR
  field_simp
  unfold Mc Kc Zc; ring

lemma Mc_pos {c δ : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) : 0 < Mc c δ := by
  unfold Mc
  have hp : 0 < 1 - δ := by linarith
  have h43 : 0 < 4 - 3 * δ := by linarith
  have := mul_pos (mul_pos hc hc) hp
  have := mul_pos (mul_pos hc hδ0) h43
  nlinarith [mul_pos hδ0 hδ0]

lemma Fc_pos {c δ : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) : 0 < Fc c δ := by
  unfold Fc
  have hp : 0 < 1 - δ := by linarith
  have := mul_pos (mul_pos hc hc) hp
  have := mul_pos (mul_pos hc hδ0) hp
  nlinarith [mul_pos hδ0 hδ0]

lemma kRv_pos {c δ : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) : 0 < kRv c δ := by
  unfold kRv; have := Mc_pos hc hδ0 hδ1; have := Zc_pos hc hδ0 hδ1; positivity

lemma facts_N {pol : Policy} {v c δ : ℝ} (P : RetailPrivacy.SupplyChain.Profile)
    (hREE : ∀ p, IsREE pol false v c δ p (P.resp false p).1 (P.resp false p).2) :
    (∀ w p, RetailPrivacy.SupplyChain.retailerProfit false v c δ w p (P.resp false p) =
      gG 1 0 v w (v - p)) ∧
    (∀ w p, RetailPrivacy.SupplyChain.supplierProfit false v δ w p (P.resp false p) =
      w * gD 1 (v - p)) ∧
    (∀ p, 0 < v - p → v - p ≤ 1 →
      consumerSurplus false v δ p (P.resp false p).2 = 1 * ((v - p) / 1) ^ 2 / 2) := by
  have hr : ∀ p, (P.resp false p).1 = 0 ∧ (P.resp false p).2 = 0 := by
    intro p; have := hREE p; unfold IsREE at this; simpa using this
  refine ⟨fun w p => ?_, fun w p => ?_, fun p h0 h1 => ?_⟩
  · unfold RetailPrivacy.SupplyChain.retailerProfit gG
    rw [demand_false, (hr p).1, (hr p).2]; unfold dataProfit; ring
  · unfold RetailPrivacy.SupplyChain.supplierProfit; rw [demand_false]
  · rw [cs_false h0.le h1]; ring

lemma facts_CT {v c δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : RetailPrivacy.SupplyChain.Profile)
    (hREE : ∀ p, IsREE .C true v c δ p (P.resp true p).1 (P.resp true p).2) :
    (∀ w p, RetailPrivacy.SupplyChain.retailerProfit true v c δ w p (P.resp true p) =
      gG (1 - δ) 0 v w (v - p)) ∧
    (∀ w p, RetailPrivacy.SupplyChain.supplierProfit true v δ w p (P.resp true p) =
      w * gD (1 - δ) (v - p)) ∧
    (∀ p, 0 < v - p → v - p ≤ 1 - δ →
      consumerSurplus true v δ p (P.resp true p).2 = (1 - δ) * ((v - p) / (1 - δ)) ^ 2 / 2) := by
  have hr : ∀ p, (P.resp true p).2 = 0 := by
    intro p; have := hREE p; unfold IsREE at this; simp at this; exact this.1
  refine ⟨fun w p => ?_, fun w p => ?_, fun p h0 h1 => ?_⟩
  · unfold RetailPrivacy.SupplyChain.retailerProfit gG
    rw [hr p, demand_C hδ0 hδ1]; unfold dataProfit; ring
  · unfold RetailPrivacy.SupplyChain.supplierProfit; rw [hr p, demand_C hδ0 hδ1]
  · rw [hr p, cs_C hδ0 hδ1 h0 h1]

lemma facts_RT {v c δ : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : RetailPrivacy.SupplyChain.Profile)
    (hREE : ∀ p, IsREE .R true v c δ p (P.resp true p).1 (P.resp true p).2) :
    (∀ w p, RetailPrivacy.SupplyChain.retailerProfit true v c δ w p (P.resp true p) =
      gG (aR c δ) (c * δ ^ 2 / Kc c δ ^ 2) v w (v - p)) ∧
    (∀ w p, RetailPrivacy.SupplyChain.supplierProfit true v δ w p (P.resp true p) =
      w * gD (aR c δ) (v - p)) ∧
    (∀ p, 0 < v - p → v - p ≤ aR c δ →
      consumerSurplus true v δ p (P.resp true p).2 =
        Fc c δ / Zc c δ ^ 2 * ((v - p) / aR c δ) ^ 2 / 2) := by
  have hr : ∀ p, P.resp true p = (sR c δ (v - p), rR c δ (v - p)) := by
    intro p
    obtain ⟨h1, h2⟩ := ree_R_unique hc hδ0 hδ1 (hREE p)
    exact Prod.ext h1 h2
  refine ⟨fun w p => ?_, fun w p => ?_, fun p h0 h1 => ?_⟩
  · unfold RetailPrivacy.SupplyChain.retailerProfit gG
    rw [hr p]; dsimp only
    rw [demand_R hc hδ0 hδ1, data_R hc hδ0 hδ1]; ring
  · unfold RetailPrivacy.SupplyChain.supplierProfit; rw [hr p]; dsimp only
    rw [demand_R hc hδ0 hδ1]
  · rw [hr p]; dsimp only; rw [cs_R hc hδ0 hδ1 h0 h1]

lemma eR_nonneg {c δ : ℝ} (hc : 0 < c) : 0 ≤ c * δ ^ 2 / Kc c δ ^ 2 :=
  div_nonneg (mul_nonneg hc.le (sq_nonneg δ)) (sq_nonneg _)

lemma values_R {v c δ : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v)
    (P : RetailPrivacy.SupplyChain.Profile)
    (hREE : ∀ ℓ p, IsREE .R ℓ v c δ p (P.resp ℓ p).1 (P.resp ℓ p).2)
    (hBR : ∀ ℓ w p', RetailPrivacy.SupplyChain.retailerProfit ℓ v c δ w p' (P.resp ℓ p') ≤
      RetailPrivacy.SupplyChain.retailerProfit ℓ v c δ w (P.price ℓ w) (P.resp ℓ (P.price ℓ w)))
    (hS : ∀ ℓ w', RetailPrivacy.SupplyChain.supplierProfit ℓ v δ w' (P.price ℓ w')
      (P.resp ℓ (P.price ℓ w')) ≤ RetailPrivacy.SupplyChain.supplierValue v δ P ℓ) :
    (RetailPrivacy.SupplyChain.retailerValue v c δ P true = retS (kRv c δ) v ∧
      RetailPrivacy.SupplyChain.supplierValue v δ P true = supS (kRv c δ) v ∧
      RetailPrivacy.SupplyChain.surplusValue v δ P true = csS (Fc c δ / Zc c δ ^ 2) (kRv c δ) v) ∧
    (RetailPrivacy.SupplyChain.retailerValue v c δ P false = retS 1 v ∧
      RetailPrivacy.SupplyChain.supplierValue v δ P false = supS 1 v ∧
      RetailPrivacy.SupplyChain.surplusValue v δ P false = csS 1 1 v) := by
  obtain ⟨t1, t2, t3⟩ := facts_RT hc hδ0 hδ1 P (hREE true)
  obtain ⟨f1, f2, f3⟩ := facts_N P (hREE false)
  exact ⟨onpath_gen (aR_pos hc hδ0 hδ1) (eR_nonneg hc) (kRv_eq hc hδ0 hδ1) (kRv_pos hc hδ0 hδ1) hv
      (fun w p => RetailPrivacy.SupplyChain.retailerProfit true v c δ w p (P.resp true p))
      (fun w p => RetailPrivacy.SupplyChain.supplierProfit true v δ w p (P.resp true p))
      (fun p => consumerSurplus true v δ p (P.resp true p).2)
      (P.price true) (P.wholesale true) t1 t2 t3 (hBR true) (hS true),
    onpath_gen one_pos le_rfl (by ring) one_pos hv
      (fun w p => RetailPrivacy.SupplyChain.retailerProfit false v c δ w p (P.resp false p))
      (fun w p => RetailPrivacy.SupplyChain.supplierProfit false v δ w p (P.resp false p))
      (fun p => consumerSurplus false v δ p (P.resp false p).2)
      (P.price false) (P.wholesale false) f1 f2 f3 (hBR false) (hS false)⟩

lemma values_C {v c δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v)
    (P : RetailPrivacy.SupplyChain.Profile)
    (hREE : ∀ ℓ p, IsREE .C ℓ v c δ p (P.resp ℓ p).1 (P.resp ℓ p).2)
    (hBR : ∀ ℓ w p', RetailPrivacy.SupplyChain.retailerProfit ℓ v c δ w p' (P.resp ℓ p') ≤
      RetailPrivacy.SupplyChain.retailerProfit ℓ v c δ w (P.price ℓ w) (P.resp ℓ (P.price ℓ w)))
    (hS : ∀ ℓ w', RetailPrivacy.SupplyChain.supplierProfit ℓ v δ w' (P.price ℓ w')
      (P.resp ℓ (P.price ℓ w')) ≤ RetailPrivacy.SupplyChain.supplierValue v δ P ℓ) :
    (RetailPrivacy.SupplyChain.retailerValue v c δ P true = retS (1 - δ) v ∧
      RetailPrivacy.SupplyChain.supplierValue v δ P true = supS (1 - δ) v ∧
      RetailPrivacy.SupplyChain.surplusValue v δ P true = csS (1 - δ) (1 - δ) v) ∧
    (RetailPrivacy.SupplyChain.retailerValue v c δ P false = retS 1 v ∧
      RetailPrivacy.SupplyChain.supplierValue v δ P false = supS 1 v ∧
      RetailPrivacy.SupplyChain.surplusValue v δ P false = csS 1 1 v) := by
  obtain ⟨t1, t2, t3⟩ := facts_CT hδ0 hδ1 P (hREE true)
  obtain ⟨f1, f2, f3⟩ := facts_N P (hREE false)
  have hp : (0:ℝ) < 1 - δ := by linarith
  exact ⟨onpath_gen hp le_rfl (by ring) hp hv
      (fun w p => RetailPrivacy.SupplyChain.retailerProfit true v c δ w p (P.resp true p))
      (fun w p => RetailPrivacy.SupplyChain.supplierProfit true v δ w p (P.resp true p))
      (fun p => consumerSurplus true v δ p (P.resp true p).2)
      (P.price true) (P.wholesale true) t1 t2 t3 (hBR true) (hS true),
    onpath_gen one_pos le_rfl (by ring) one_pos hv
      (fun w p => RetailPrivacy.SupplyChain.retailerProfit false v c δ w p (P.resp false p))
      (fun w p => RetailPrivacy.SupplyChain.supplierProfit false v δ w p (P.resp false p))
      (fun p => consumerSurplus false v δ p (P.resp false p).2)
      (P.price false) (P.wholesale false) f1 f2 f3 (hBR false) (hS false)⟩

/-! ### existence -/

noncomputable def profR (v c δ : ℝ) : RetailPrivacy.SupplyChain.Profile where
  collect := decide (retS 1 v ≤ retS (kRv c δ) v)
  wholesale := fun ℓ => if ℓ then wS (kRv c δ) v else wS 1 v
  price := fun ℓ w => if ℓ then v - gX (aR c δ) (kRv c δ) v w else v - gX 1 1 v w
  resp := fun ℓ p => if ℓ then (sR c δ (v - p), rR c δ (v - p)) else (0, 0)

noncomputable def profC (v : ℝ) (δ : ℝ) : RetailPrivacy.SupplyChain.Profile where
  collect := decide (retS 1 v ≤ retS (1 - δ) v)
  wholesale := fun ℓ => if ℓ then wS (1 - δ) v else wS 1 v
  price := fun ℓ w => if ℓ then v - gX (1 - δ) (1 - δ) v w else v - gX 1 1 v w
  resp := fun ℓ p => if ℓ then (discloseQty v δ p 0, 0) else (0, 0)

/-- the supplier's inequality in a generic subgame, from `gPhi_le` -/
lemma sup_ineq {a k v : ℝ} (ha : 0 < a) (hk0 : 0 < k) (hv : 0 < v) (w' : ℝ) :
    w' * gD a (gX a k v w') ≤ wS k v * gD a (gX a k v (wS k v)) := by
  have h1 := (gPhi_le ha hk0 hv w').1
  rw [← gPhi_wS ha hk0 hv] at h1
  exact h1

lemma collect_ok {P : RetailPrivacy.SupplyChain.Profile} {v c δ x y : ℝ}
    (hT : RetailPrivacy.SupplyChain.retailerValue v c δ P true = y)
    (hF : RetailPrivacy.SupplyChain.retailerValue v c δ P false = x)
    (hcol : P.collect = decide (x ≤ y)) (ℓ' : Bool) :
    RetailPrivacy.SupplyChain.retailerValue v c δ P ℓ' ≤
      RetailPrivacy.SupplyChain.retailerValue v c δ P P.collect := by
  by_cases hd : x ≤ y
  · have : P.collect = true := by rw [hcol]; exact decide_eq_true hd
    rw [this]; cases ℓ'
    · rw [hF, hT]; exact hd
    · exact le_rfl
  · have : P.collect = false := by rw [hcol]; exact decide_eq_false hd
    rw [this]; cases ℓ'
    · exact le_rfl
    · rw [hF, hT]; push Not at hd; exact hd.le

lemma profR_spe {v c δ : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v) :
    RetailPrivacy.SupplyChain.IsSPE .R v c δ (profR v c δ) := by
  have hREE : ∀ ℓ p, IsREE .R ℓ v c δ p ((profR v c δ).resp ℓ p).1
      ((profR v c δ).resp ℓ p).2 := by
    intro ℓ p; cases ℓ
    · simp [profR, IsREE]
    · simpa [profR] using ree_R_exists hc hδ0 hδ1 v p
  obtain ⟨t1, t2, -⟩ := facts_RT hc hδ0 hδ1 (profR v c δ) (hREE true)
  obtain ⟨f1, f2, -⟩ := facts_N (profR v c δ) (hREE false)
  have hBR : ∀ ℓ w p', RetailPrivacy.SupplyChain.retailerProfit ℓ v c δ w p'
      ((profR v c δ).resp ℓ p') ≤ RetailPrivacy.SupplyChain.retailerProfit ℓ v c δ w
      ((profR v c δ).price ℓ w) ((profR v c δ).resp ℓ ((profR v c δ).price ℓ w)) := by
    intro ℓ w p'; cases ℓ
    · rw [f1, f1]; simp only [profR, Bool.false_eq_true, ↓reduceIte, sub_sub_cancel]
      exact gG_max one_pos le_rfl (by ring) one_pos _
    · rw [t1, t1]; simp only [profR, ↓reduceIte, sub_sub_cancel]
      exact gG_max (aR_pos hc hδ0 hδ1) (eR_nonneg hc) (kRv_eq hc hδ0 hδ1) (kRv_pos hc hδ0 hδ1) _
  have hS : ∀ ℓ w', RetailPrivacy.SupplyChain.supplierProfit ℓ v δ w' ((profR v c δ).price ℓ w')
      ((profR v c δ).resp ℓ ((profR v c δ).price ℓ w')) ≤
      RetailPrivacy.SupplyChain.supplierValue v δ (profR v c δ) ℓ := by
    intro ℓ w'
    unfold RetailPrivacy.SupplyChain.supplierValue RetailPrivacy.SupplyChain.pathResp
      RetailPrivacy.SupplyChain.pathPrice RetailPrivacy.SupplyChain.pathWholesale
    cases ℓ
    · rw [f2, f2]; simp only [profR, Bool.false_eq_true, ↓reduceIte, sub_sub_cancel]
      exact sup_ineq one_pos one_pos hv w'
    · rw [t2, t2]; simp only [profR, ↓reduceIte, sub_sub_cancel]
      exact sup_ineq (aR_pos hc hδ0 hδ1) (kRv_pos hc hδ0 hδ1) hv w'
  obtain ⟨⟨r1, -, -⟩, ⟨r2, -, -⟩⟩ := values_R hc hδ0 hδ1 hv _ hREE hBR hS
  exact ⟨hREE, hBR, hS, collect_ok r1 r2 rfl⟩

lemma profC_spe {v c δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v) :
    RetailPrivacy.SupplyChain.IsSPE .C v c δ (profC v δ) := by
  have hp : (0:ℝ) < 1 - δ := by linarith
  have hREE : ∀ ℓ p, IsREE .C ℓ v c δ p ((profC v δ).resp ℓ p).1 ((profC v δ).resp ℓ p).2 := by
    intro ℓ p; cases ℓ
    · simp [profC, IsREE]
    · simp [profC, IsREE]
  obtain ⟨t1, t2, -⟩ := facts_CT hδ0 hδ1 (profC v δ) (hREE true)
  obtain ⟨f1, f2, -⟩ := facts_N (profC v δ) (hREE false)
  have hBR : ∀ ℓ w p', RetailPrivacy.SupplyChain.retailerProfit ℓ v c δ w p'
      ((profC v δ).resp ℓ p') ≤ RetailPrivacy.SupplyChain.retailerProfit ℓ v c δ w
      ((profC v δ).price ℓ w) ((profC v δ).resp ℓ ((profC v δ).price ℓ w)) := by
    intro ℓ w p'; cases ℓ
    · rw [f1, f1]; simp only [profC, Bool.false_eq_true, ↓reduceIte, sub_sub_cancel]
      exact gG_max one_pos le_rfl (by ring) one_pos _
    · rw [t1, t1]; simp only [profC, ↓reduceIte, sub_sub_cancel]
      exact gG_max hp le_rfl (by ring) hp _
  have hS : ∀ ℓ w', RetailPrivacy.SupplyChain.supplierProfit ℓ v δ w' ((profC v δ).price ℓ w')
      ((profC v δ).resp ℓ ((profC v δ).price ℓ w')) ≤
      RetailPrivacy.SupplyChain.supplierValue v δ (profC v δ) ℓ := by
    intro ℓ w'
    unfold RetailPrivacy.SupplyChain.supplierValue RetailPrivacy.SupplyChain.pathResp
      RetailPrivacy.SupplyChain.pathPrice RetailPrivacy.SupplyChain.pathWholesale
    cases ℓ
    · rw [f2, f2]; simp only [profC, Bool.false_eq_true, ↓reduceIte, sub_sub_cancel]
      exact sup_ineq one_pos one_pos hv w'
    · rw [t2, t2]; simp only [profC, ↓reduceIte, sub_sub_cancel]
      exact sup_ineq hp hp hv w'
  obtain ⟨⟨r1, -, -⟩, ⟨r2, -, -⟩⟩ := values_C hδ0 hδ1 hv _ hREE hBR hS
  exact ⟨hREE, hBR, hS, collect_ok r1 r2 rfl⟩

/-! ### parameter facts and thresholds -/

lemma param_facts {c δ : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) < Fc c δ / Zc c δ ^ 2 ∧ Fc c δ / Zc c δ ^ 2 < kRv c δ ∧ kRv c δ < 1 ∧
    kRv c δ ^ 2 < Fc c δ / Zc c δ ^ 2 ∧ (1 - δ) * (Fc c δ / Zc c δ ^ 2) < kRv c δ ^ 2 := by
  have hZ := Zc_pos hc hδ0 hδ1
  have hK := Kc_pos hc hδ0 hδ1
  have hZ2 : 0 < Zc c δ ^ 2 := by positivity
  have hp : 0 < 1 - δ := by linarith
  have eZ : Zc c δ = 2 * c + δ := rfl
  have eK : Kc c δ = 2 * c * (1 - δ) + δ := rfl
  have eM : Mc c δ = Kc c δ * Zc c δ - c * δ ^ 2 := by unfold Mc Kc Zc; ring
  have eF : Fc c δ = Kc c δ * Zc c δ - 2 * c * δ ^ 2 := by unfold Fc Kc Zc; ring
  -- polynomial facts
  have p1 : (1 - δ) * Zc c δ ^ 2 < Fc c δ := by
    have : Fc c δ - (1 - δ) * Zc c δ ^ 2 = δ ^ 3 := by unfold Fc Zc; ring
    nlinarith [pow_pos hδ0 3]
  have p2 : Fc c δ < Mc c δ := by rw [eM, eF]; nlinarith [mul_pos hc (pow_pos hδ0 2)]
  have p3 : Mc c δ < Zc c δ ^ 2 := by
    have : Zc c δ ^ 2 - Mc c δ = 4 * c ^ 2 * δ + 3 * c * δ ^ 2 := by unfold Zc Mc; ring
    nlinarith [mul_pos (pow_pos hc 2) hδ0, mul_pos hc (pow_pos hδ0 2)]
  have p4 : Mc c δ ^ 2 < Fc c δ * Zc c δ ^ 2 := by
    have e : Fc c δ * Zc c δ ^ 2 - Mc c δ ^ 2 = c * δ * (4 * c * Zc c δ ^ 2 * (1 - δ) +
        2 * δ * Zc c δ * Kc c δ - c * δ ^ 3) := by unfold Fc Mc Zc Kc; ring
    have hKd : δ < Kc c δ := by rw [eK]; nlinarith [mul_pos hc hp]
    have hZc : 2 * c < Zc c δ := by rw [eZ]; linarith
    have b1 : c * δ ^ 3 < 2 * δ * Zc c δ * Kc c δ := by
      have : 2 * δ * (2 * c) * δ ≤ 2 * δ * Zc c δ * Kc c δ := by
        have := mul_le_mul hZc.le hKd.le hδ0.le (by linarith)
        nlinarith
      nlinarith [mul_pos hc (pow_pos hδ0 2), mul_pos (mul_pos hc (pow_pos hδ0 2)) (sub_pos.2 hδ1)]
    have b2 : 0 < 4 * c * Zc c δ ^ 2 * (1 - δ) := by
      have := mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) hc) (pow_pos hZ 2)) hp; linarith
    nlinarith [mul_pos (mul_pos hc hδ0) (by linarith : (0:ℝ) < 4 * c * Zc c δ ^ 2 * (1 - δ) +
        2 * δ * Zc c δ * Kc c δ - c * δ ^ 3)]
  have p5 : (1 - δ) * Fc c δ * Zc c δ ^ 2 < Mc c δ ^ 2 := by
    have e : Mc c δ ^ 2 - (1 - δ) * Fc c δ * Zc c δ ^ 2 = δ ^ 2 * (Kc c δ * Zc c δ * δ +
        c ^ 2 * δ ^ 2 + 2 * c * (1 - δ) * Zc c δ ^ 2) := by unfold Fc Mc Zc Kc; ring
    have : 0 < Kc c δ * Zc c δ * δ + c ^ 2 * δ ^ 2 + 2 * c * (1 - δ) * Zc c δ ^ 2 := by
      have h1 := mul_pos (mul_pos hK hZ) hδ0
      have h2 := mul_pos (mul_pos (mul_pos (two_pos : (0:ℝ) < 2) hc) hp) (pow_pos hZ 2)
      nlinarith [sq_nonneg (c * δ)]
    nlinarith [mul_pos (pow_pos hδ0 2) this]
  unfold kRv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hZ2]; linarith
  · rw [div_lt_div_iff_of_pos_right hZ2]; exact p2
  · rw [div_lt_one hZ2]; exact p3
  · rw [div_pow, div_lt_div_iff₀ (by positivity) hZ2]
    nlinarith [mul_lt_mul_of_pos_right p4 hZ2]
  · rw [div_pow, ← mul_div_assoc, div_lt_div_iff₀ hZ2 (by positivity)]
    nlinarith [mul_lt_mul_of_pos_right p5 hZ2]

lemma sq_lt_of {a b : ℝ} (ha : 0 ≤ a) (h : a < b) : a ^ 2 < b ^ 2 := by nlinarith

lemma T_sq {c δ : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (4 * Real.sqrt (1 - δ)) ^ 2 = 16 * (1 - δ) ∧
    (4 * Real.sqrt (Fc c δ) / Zc c δ) ^ 2 = 16 * (Fc c δ / Zc c δ ^ 2) ∧
    (4 * Real.sqrt ((1 - δ) * Mc c δ) / Zc c δ) ^ 2 = 16 * (1 - δ) * kRv c δ ∧
    (4 * Mc c δ * Real.sqrt (1 - δ) / (Zc c δ * Real.sqrt (Fc c δ))) ^ 2 =
      16 * (1 - δ) * kRv c δ ^ 2 / (Fc c δ / Zc c δ ^ 2) ∧
    (4 * Real.sqrt (Mc c δ) / Zc c δ) ^ 2 = 16 * kRv c δ := by
  have hZ := Zc_pos hc hδ0 hδ1
  have hM := Mc_pos hc hδ0 hδ1
  have hF := Fc_pos hc hδ0 hδ1
  have hp : 0 < 1 - δ := by linarith
  have s1 := Real.sq_sqrt hp.le
  have s2 := Real.sq_sqrt hF.le
  have s3 := Real.sq_sqrt (mul_pos hp hM).le
  have s4 := Real.sq_sqrt hM.le
  unfold kRv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [mul_pow, s1]; ring
  · simp only [div_pow, mul_pow, s2]; ring
  · simp only [div_pow, mul_pow, s3]; ring
  · simp only [div_pow, mul_pow, s1, s2]; field_simp; try ring
  · simp only [div_pow, mul_pow, s4]; ring

lemma T_nonneg {c δ : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 ≤ 4 * Real.sqrt (Fc c δ) / Zc c δ ∧ 0 ≤ 4 * Real.sqrt ((1 - δ) * Mc c δ) / Zc c δ ∧
    0 ≤ 4 * Mc c δ * Real.sqrt (1 - δ) / (Zc c δ * Real.sqrt (Fc c δ)) := by
  have hZ := Zc_pos hc hδ0 hδ1
  have hM := Mc_pos hc hδ0 hδ1
  refine ⟨by positivity, by positivity, by positivity⟩

end RPSCH

set_option maxHeartbeats 1000000 in
open RetailPrivacy.SupplyChain in
theorem RPSCH_claims (c δ v : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v) :
    ∀ PR PC : Profile, IsSPE .R v c δ PR → IsSPE .C v c δ PC →
      (4 * Real.sqrt (1 - δ) < v ∧ v < 4 * Real.sqrt (RetailPrivacy.SingleFirm.Fc c δ) / RetailPrivacy.SingleFirm.Zc c δ →
          eqCS v δ PC < eqCS v δ PR ∧ eqRetailer v c δ PC < eqRetailer v c δ PR ∧ eqSupplier v δ PC < eqSupplier v δ PR) ∧
      (v < 4 * Real.sqrt ((1 - δ) * RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ →
          eqCS v δ PR < eqCS v δ PC ∧ eqRetailer v c δ PR < eqRetailer v c δ PC ∧ eqSupplier v δ PR < eqSupplier v δ PC) ∧
      (4 * Real.sqrt ((1 - δ) * RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ < v ∧ v < 4 * RetailPrivacy.SingleFirm.Mc c δ * Real.sqrt (1 - δ) / (RetailPrivacy.SingleFirm.Zc c δ * Real.sqrt (RetailPrivacy.SingleFirm.Fc c δ)) →
          eqRetailer v c δ PC < eqRetailer v c δ PR ∧ eqCS v δ PR < eqCS v δ PC ∧ eqSupplier v δ PR < eqSupplier v δ PC) ∧
      (4 * RetailPrivacy.SingleFirm.Mc c δ * Real.sqrt (1 - δ) / (RetailPrivacy.SingleFirm.Zc c δ * Real.sqrt (RetailPrivacy.SingleFirm.Fc c δ)) < v ∧ v < 4 * Real.sqrt (1 - δ) →
          eqRetailer v c δ PC < eqRetailer v c δ PR ∧ eqCS v δ PC < eqCS v δ PR ∧ eqSupplier v δ PR < eqSupplier v δ PC) ∧
      (4 * Real.sqrt (RetailPrivacy.SingleFirm.Fc c δ) / RetailPrivacy.SingleFirm.Zc c δ < v ∧ v < 4 * Real.sqrt (RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ →
          eqCS v δ PR < eqCS v δ PC ∧ eqRetailer v c δ PC < eqRetailer v c δ PR ∧ eqSupplier v δ PC < eqSupplier v δ PR) := by
  intro PR PC hR hC
  obtain ⟨hR1, hR2, hR3, hR4⟩ := hR
  obtain ⟨hC1, hC2, hC3, hC4⟩ := hC
  obtain ⟨⟨rT, sT, cT⟩, ⟨rF, sF, cF⟩⟩ := RPSCH.values_R hc hδ0 hδ1 hv PR hR1 hR2 hR3
  obtain ⟨⟨rT', sT', cT'⟩, ⟨rF', sF', cF'⟩⟩ := RPSCH.values_C hδ0 hδ1 hv PC hC1 hC2 hC3
  obtain ⟨f1, f2, f3, f4, f5⟩ := RPSCH.param_facts hc hδ0 hδ1
  obtain ⟨q3, q4, q1, q2, q5⟩ := RPSCH.T_sq hc hδ0 hδ1
  obtain ⟨n4, n1, n2⟩ := RPSCH.T_nonneg hc hδ0 hδ1
  have hp : (0:ℝ) < 1 - δ := by linarith
  have hp1 : 1 - δ < 1 := by linarith
  have hρ0 : 0 < RetailPrivacy.SingleFirm.Fc c δ / RetailPrivacy.SingleFirm.Zc c δ ^ 2 := by
    linarith
  have hk0 : 0 < RPSCH.kRv c δ := by linarith
  have colR : v ^ 2 < 16 * RPSCH.kRv c δ → PR.collect = true := by
    intro h
    by_contra hne
    have hf : PR.collect = false := by simpa using hne
    have := hR4 true
    rw [hf, rT, rF] at this
    exact absurd this (not_le.mpr (RPSCH.R_collects hp hp1 f1 f2 f3 f4 f5 hv h))
  have colC1 : v ^ 2 < 16 * (1 - δ) → PC.collect = true := by
    intro h
    by_contra hne
    have hf : PC.collect = false := by simpa using hne
    have := hC4 true
    rw [hf, rT', rF'] at this
    exact absurd this (not_le.mpr (RPSCH.C_collects hp hp1 f1 f2 f3 f4 f5 hv h))
  have colC0 : 16 * (1 - δ) < v ^ 2 → v ^ 2 < 16 → PC.collect = false := by
    intro h h'
    by_contra hne
    have hf : PC.collect = true := by simpa using hne
    have := hC4 false
    rw [hf, rT', rF'] at this
    exact absurd this (not_le.mpr (RPSCH.C_declines hp hp1 f1 f2 f3 f4 f5 hv h h'))
  unfold eqCS eqRetailer eqSupplier
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun h => ?_, fun ⟨h1, h2⟩ => ?_, fun ⟨h1, h2⟩ => ?_,
    fun ⟨h1, h2⟩ => ?_⟩
  · -- claim 1
    have a1 := RPSCH.sq_lt_of (by positivity) h1
    have a2 := RPSCH.sq_lt_of hv.le h2
    rw [q3] at a1; rw [q4] at a2
    rw [colR (by linarith), colC0 a1 (by linarith), cT, rT, sT, cF', rF', sF']
    exact RPSCH.claim1 hp hp1 f1 f2 f3 f4 f5 hv a1 a2
  · -- claim 2
    have a2 := RPSCH.sq_lt_of hv.le h
    rw [q1] at a2
    have b1 : v ^ 2 < 16 * RPSCH.kRv c δ := by
      have := mul_lt_mul_of_pos_right hp1 hk0; linarith
    have b2 : v ^ 2 < 16 * (1 - δ) := by
      have := mul_lt_mul_of_pos_left f3 hp; linarith
    rw [colR b1, colC1 b2, cT, rT, sT, cT', rT', sT']
    exact RPSCH.claim2 hp hp1 f1 f2 f3 f4 f5 hv a2
  · -- claim 3
    have a1 := RPSCH.sq_lt_of n1 h1
    have a2 := RPSCH.sq_lt_of hv.le h2
    rw [q1] at a1; rw [q2] at a2
    have a2' := (lt_div_iff₀ hρ0).mp a2
    have hh : (1 - δ) * RPSCH.kRv c δ <
        RetailPrivacy.SingleFirm.Fc c δ / RetailPrivacy.SingleFirm.Zc c δ ^ 2 := by
      have := mul_lt_mul_of_pos_left f3 hp; linarith
    have b1 : v ^ 2 < 16 * RPSCH.kRv c δ := by
      by_contra hb; push Not at hb
      linarith [mul_le_mul_of_nonneg_right hb hρ0.le,
        mul_lt_mul_of_pos_left hh (by positivity : (0:ℝ) < 16 * RPSCH.kRv c δ)]
    have b2 : v ^ 2 < 16 * (1 - δ) := by
      by_contra hb; push Not at hb
      linarith [mul_le_mul_of_nonneg_right hb hρ0.le,
        mul_lt_mul_of_pos_left f4 (by linarith : (0:ℝ) < 16 * (1 - δ))]
    rw [colR b1, colC1 b2, cT, rT, sT, cT', rT', sT']
    exact RPSCH.claim3 hp hp1 f1 f2 f3 f4 f5 hv a1 a2
  · -- claim 4
    have a1 := RPSCH.sq_lt_of n2 h1
    have a2 := RPSCH.sq_lt_of hv.le h2
    rw [q2] at a1; rw [q3] at a2
    have b1 : v ^ 2 < 16 * RPSCH.kRv c δ := by linarith
    rw [colR b1, colC1 a2, cT, rT, sT, cT', rT', sT']
    exact RPSCH.claim4 hp hp1 f1 f2 f3 f4 f5 hv a1 a2
  · -- claim 5
    have a1 := RPSCH.sq_lt_of n4 h1
    have a2 := RPSCH.sq_lt_of hv.le h2
    rw [q4] at a1; rw [q5] at a2
    rw [colR a2, colC0 (by linarith) (by linarith), cT, rT, sT, cF', rF', sF']
    exact RPSCH.claim5 hp hp1 f1 f2 f3 f4 f5 hv a1 a2

open RetailPrivacy.SupplyChain in
theorem solution (c δ v : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v) :
    (∃ P : Profile, IsSPE .R v c δ P) ∧ (∃ P : Profile, IsSPE .C v c δ P) ∧
    ∀ PR PC : Profile, IsSPE .R v c δ PR → IsSPE .C v c δ PC →
      (4 * Real.sqrt (1 - δ) < v ∧ v < 4 * Real.sqrt (RetailPrivacy.SingleFirm.Fc c δ) / RetailPrivacy.SingleFirm.Zc c δ →
          eqCS v δ PC < eqCS v δ PR ∧ eqRetailer v c δ PC < eqRetailer v c δ PR ∧ eqSupplier v δ PC < eqSupplier v δ PR) ∧
      (v < 4 * Real.sqrt ((1 - δ) * RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ →
          eqCS v δ PR < eqCS v δ PC ∧ eqRetailer v c δ PR < eqRetailer v c δ PC ∧ eqSupplier v δ PR < eqSupplier v δ PC) ∧
      (4 * Real.sqrt ((1 - δ) * RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ < v ∧ v < 4 * RetailPrivacy.SingleFirm.Mc c δ * Real.sqrt (1 - δ) / (RetailPrivacy.SingleFirm.Zc c δ * Real.sqrt (RetailPrivacy.SingleFirm.Fc c δ)) →
          eqRetailer v c δ PC < eqRetailer v c δ PR ∧ eqCS v δ PR < eqCS v δ PC ∧ eqSupplier v δ PR < eqSupplier v δ PC) ∧
      (4 * RetailPrivacy.SingleFirm.Mc c δ * Real.sqrt (1 - δ) / (RetailPrivacy.SingleFirm.Zc c δ * Real.sqrt (RetailPrivacy.SingleFirm.Fc c δ)) < v ∧ v < 4 * Real.sqrt (1 - δ) →
          eqRetailer v c δ PC < eqRetailer v c δ PR ∧ eqCS v δ PC < eqCS v δ PR ∧ eqSupplier v δ PR < eqSupplier v δ PC) ∧
      (4 * Real.sqrt (RetailPrivacy.SingleFirm.Fc c δ) / RetailPrivacy.SingleFirm.Zc c δ < v ∧ v < 4 * Real.sqrt (RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ →
          eqCS v δ PR < eqCS v δ PC ∧ eqRetailer v c δ PC < eqRetailer v c δ PR ∧ eqSupplier v δ PC < eqSupplier v δ PR) := by
  exact ⟨⟨RPSCH.profR v c δ, RPSCH.profR_spe hc hδ0 hδ1 hv⟩, ⟨RPSCH.profC v δ, RPSCH.profC_spe hδ0 hδ1 hv⟩,
    RPSCH_claims c δ v hc hδ0 hδ1 hv⟩
