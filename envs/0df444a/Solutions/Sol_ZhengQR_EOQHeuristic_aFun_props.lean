-- Prove2me | solution 1 for ZhengQR.EOQHeuristic.aFun_props
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:44:14.7343+00:00
-- url     : https://prove2.me/submissions/27d69d9c-3a8c-4e39-821f-15c257cc074d

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

/-- Left endpoint of the sublevel interval of length `Q` (with `minPt` at `Q ≤ 0`). -/
noncomputable def aux_zqr_aPt (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  if 0 < Q then reorderPt G lam K Q else minPt G

/-- `∫ G` over the optimal window of length `Q`. -/
noncomputable def aux_zqr_I (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  ∫ y in aux_zqr_aPt G lam K Q..aux_zqr_aPt G lam K Q + Q, G y

section AuxZQR

variable {G : ℝ → ℝ}

lemma aux_zqr_minPt_le (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (z : ℝ) : G (minPt G) ≤ G z := by
  have hex : ∃ y, ∀ z, G y ≤ G z := hu.exists
  unfold minPt
  rw [dif_pos hex]
  exact hex.choose_spec z

lemma aux_zqr_minPt_lt (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (z : ℝ) (hz : z ≠ minPt G) :
    G (minPt G) < G z := by
  by_contra h
  push Not at h
  apply hz
  have h1 := aux_zqr_minPt_le hu
  have hz' : ∀ w, G z ≤ G w := fun w => h.trans (h1 w)
  exact hu.unique hz' h1

lemma aux_zqr_anti (hconv : ConvexOn ℝ Set.univ G) (hu : ∃! y : ℝ, ∀ z, G y ≤ G z)
    {x y : ℝ} (hxy : x < y) (hy : y ≤ minPt G) : G y < G x := by
  rcases eq_or_lt_of_le hy with h | h
  · rw [h]; exact aux_zqr_minPt_lt hu x (by rw [← h]; exact hxy.ne)
  · have hs := hconv.slope_mono_adjacent (Set.mem_univ x) (Set.mem_univ (minPt G)) hxy h
    have h2 : G (minPt G) < G y := aux_zqr_minPt_lt hu y h.ne
    have h3 : (G (minPt G) - G y) / (minPt G - y) < 0 :=
      div_neg_of_neg_of_pos (by linarith) (by linarith)
    by_contra hc
    push Not at hc
    have : 0 ≤ (G y - G x) / (y - x) := div_nonneg (by linarith) (by linarith)
    linarith

lemma aux_zqr_mono (hconv : ConvexOn ℝ Set.univ G) (hu : ∃! y : ℝ, ∀ z, G y ≤ G z)
    {x y : ℝ} (hxy : x < y) (hx : minPt G ≤ x) : G x < G y := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]; exact aux_zqr_minPt_lt hu y (by rw [h]; exact hxy.ne')
  · have hs := hconv.slope_mono_adjacent (Set.mem_univ (minPt G)) (Set.mem_univ y) h hxy
    have h2 : G (minPt G) < G x := aux_zqr_minPt_lt hu x h.ne'
    have h3 : 0 < (G x - G (minPt G)) / (x - minPt G) := div_pos (by linarith) (by linarith)
    by_contra hc
    push Not at hc
    have : (G y - G x) / (y - x) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith

lemma aux_zqr_anti_le (hconv : ConvexOn ℝ Set.univ G) (hu : ∃! y : ℝ, ∀ z, G y ≤ G z)
    {x y : ℝ} (hxy : x ≤ y) (hy : y ≤ minPt G) : G y ≤ G x := by
  rcases eq_or_lt_of_le hxy with h | h
  · rw [h]
  · exact (aux_zqr_anti hconv hu h hy).le

lemma aux_zqr_mono_le (hconv : ConvexOn ℝ Set.univ G) (hu : ∃! y : ℝ, ∀ z, G y ≤ G z)
    {x y : ℝ} (hxy : x ≤ y) (hx : minPt G ≤ x) : G x ≤ G y := by
  rcases eq_or_lt_of_le hxy with h | h
  · rw [h]
  · exact (aux_zqr_mono hconv hu h hx).le

lemma aux_zqr_sign (hconv : ConvexOn ℝ Set.univ G) (hu : ∃! y : ℝ, ∀ z, G y ≤ G z)
    {Q r : ℝ} (hQ : 0 < Q) (hr : G (r + Q) = G r) : r < minPt G ∧ minPt G < r + Q := by
  constructor
  · by_contra h
    push Not at h
    have := aux_zqr_mono hconv hu (show r < r + Q by linarith) h
    linarith
  · by_contra h
    push Not at h
    have := aux_zqr_anti hconv hu (show r < r + Q by linarith) h
    linarith

lemma aux_zqr_phi_pos (hconv : ConvexOn ℝ Set.univ G) (hu : ∃! y : ℝ, ∀ z, G y ≤ G z)
    {Q r x : ℝ} (hQ : 0 < Q) (hr : G (r + Q) = G r) (hx : r < x) : G x < G (x + Q) := by
  obtain ⟨h1, h2⟩ := aux_zqr_sign hconv hu hQ hr
  by_cases hxm : x ≤ minPt G
  · have a1 := aux_zqr_anti hconv hu hx hxm
    have a2 := aux_zqr_mono hconv hu (show r + Q < x + Q by linarith) h2.le
    linarith
  · push Not at hxm
    exact aux_zqr_mono hconv hu (show x < x + Q by linarith) hxm.le

lemma aux_zqr_phi_neg (hconv : ConvexOn ℝ Set.univ G) (hu : ∃! y : ℝ, ∀ z, G y ≤ G z)
    {Q r x : ℝ} (hQ : 0 < Q) (hr : G (r + Q) = G r) (hx : x < r) : G (x + Q) < G x := by
  obtain ⟨h1, h2⟩ := aux_zqr_sign hconv hu hQ hr
  by_cases hxm : x + Q ≤ minPt G
  · exact aux_zqr_anti hconv hu (show x < x + Q by linarith) hxm
  · push Not at hxm
    have a1 := aux_zqr_anti hconv hu hx h1.le
    have a2 := aux_zqr_mono hconv hu (show x + Q < r + Q by linarith) hxm.le
    linarith

lemma aux_zqr_zero_unique (hconv : ConvexOn ℝ Set.univ G) (hu : ∃! y : ℝ, ∀ z, G y ≤ G z)
    {Q r s : ℝ} (hQ : 0 < Q) (hr : G (r + Q) = G r) (hs : G (s + Q) = G s) : r = s := by
  rcases lt_trichotomy r s with h | h | h
  · have := aux_zqr_phi_pos hconv hu hQ hr h; linarith
  · exact h
  · have := aux_zqr_phi_pos hconv hu hQ hs h; linarith

lemma aux_zqr_zero_exists (hc : Continuous G) (hu : ∃! y : ℝ, ∀ z, G y ≤ G z)
    {Q : ℝ} (hQ : 0 < Q) : ∃ r, G (r + Q) = G r := by
  have hle := aux_zqr_minPt_le hu
  have hcont : ContinuousOn (fun r => G (r + Q) - G r) (Set.Icc (minPt G - Q) (minPt G)) :=
    ((hc.comp (continuous_add_const Q)).sub hc).continuousOn
  have hivt := intermediate_value_Icc (show minPt G - Q ≤ minPt G by linarith) hcont
  have h0 : (0:ℝ) ∈ Set.Icc ((fun r => G (r + Q) - G r) (minPt G - Q))
      ((fun r => G (r + Q) - G r) (minPt G)) := by
    simp only [Set.mem_Icc, sub_add_cancel]
    constructor
    · linarith [hle (minPt G - Q)]
    · linarith [hle (minPt G + Q)]
  obtain ⟨r, _, hr⟩ := hivt h0
  exact ⟨r, by simp only at hr; linarith⟩

lemma aux_zqr_J_diff (hc : Continuous G) (Q r r' : ℝ) :
    (∫ y in r'..r' + Q, G y) - (∫ y in r..r + Q, G y) = ∫ x in r..r', (G (x + Q) - G x) := by
  have hi : ∀ a b, IntervalIntegrable G volume a b := fun a b => hc.intervalIntegrable a b
  have hcQ : Continuous (fun x => G (x + Q)) := hc.comp (continuous_add_const Q)
  rw [intervalIntegral.integral_sub (hcQ.intervalIntegrable _ _) (hi _ _),
    intervalIntegral.integral_comp_add_right G Q]
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hi r r') (hi r' (r' + Q))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hi r (r + Q)) (hi (r + Q) (r' + Q))
  linarith

lemma aux_zqr_J_lt (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) {Q r r' : ℝ} (hQ : 0 < Q) (hr : G (r + Q) = G r)
    (hne : r' ≠ r) : (∫ y in r..r + Q, G y) < ∫ y in r'..r' + Q, G y := by
  have hd := aux_zqr_J_diff hc Q r r'
  have hcQ : Continuous (fun x => G (x + Q)) := hc.comp (continuous_add_const Q)
  rcases lt_or_gt_of_ne hne with h | h
  · have hpos : 0 < ∫ x in r'..r, (G x - G (x + Q)) := by
      apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ h
      · exact (hc.sub hcQ).intervalIntegrable _ _
      · intro x hx
        have := aux_zqr_phi_neg hconv hu hQ hr hx.2
        linarith
    have e : ∫ x in r'..r, (G x - G (x + Q)) = ∫ x in r..r', (G (x + Q) - G x) := by
      rw [intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]
      congr 1
      ext x
      ring
    linarith
  · have hpos : 0 < ∫ x in r..r', (G (x + Q) - G x) := by
      apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ h
      · exact (hcQ.sub hc).intervalIntegrable _ _
      · intro x hx
        have := aux_zqr_phi_pos hconv hu hQ hr hx.1
        linarith
    linarith

lemma aux_zqr_reorder_spec (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (lam K : ℝ) {Q : ℝ} (hQ : 0 < Q) :
    G (reorderPt G lam K Q + Q) = G (reorderPt G lam K Q) := by
  obtain ⟨r0, hr0⟩ := aux_zqr_zero_exists hc hu hQ
  have hopt : IsOptReorder G lam K Q r0 := by
    intro r'
    unfold qrCost
    rcases eq_or_ne r' r0 with h | h
    · rw [h]
    · have := aux_zqr_J_lt hc hconv hu hQ hr0 h
      apply div_le_div_of_nonneg_right _ hQ.le
      linarith
  have huniq : ∀ r, IsOptReorder G lam K Q r → r = r0 := by
    intro r hr
    by_contra hne
    have h1 := hr r0
    have := aux_zqr_J_lt hc hconv hu hQ hr0 hne
    unfold qrCost at h1
    have h2 := div_lt_div_of_pos_right
      (show lam * K + ∫ y in r0..r0 + Q, G y < lam * K + ∫ y in r..r + Q, G y by linarith) hQ
    linarith
  have heq : reorderPt G lam K Q = r0 := by
    unfold reorderPt
    rw [dif_pos ⟨r0, hopt⟩]
    exact huniq _ (Exists.choose_spec _)
  rw [heq]
  exact hr0

lemma aux_zqr_zero_nest (hconv : ConvexOn ℝ Set.univ G) (hu : ∃! y : ℝ, ∀ z, G y ≤ G z)
    {Q1 Q2 r1 r2 : ℝ} (h1 : 0 < Q1) (h12 : Q1 < Q2)
    (hr1 : G (r1 + Q1) = G r1) (hr2 : G (r2 + Q2) = G r2) : r2 < r1 ∧ r1 + Q1 < r2 + Q2 := by
  have hQ2 : 0 < Q2 := h1.trans h12
  obtain ⟨s1, s2⟩ := aux_zqr_sign hconv hu h1 hr1
  constructor
  · by_contra h
    push Not at h
    have hA : G r1 < G (r1 + Q2) := by
      rw [← hr1]; exact aux_zqr_mono hconv hu (by linarith) s2.le
    rcases eq_or_lt_of_le h with h' | h'
    · rw [h'] at hA; linarith
    · have := aux_zqr_phi_neg hconv hu hQ2 hr2 h'; linarith
  · by_contra h
    push Not at h
    have hxQ : r1 + Q1 - Q2 + Q2 = r1 + Q1 := by ring
    have hB : G (r1 + Q1 - Q2 + Q2) < G (r1 + Q1 - Q2) := by
      rw [hxQ, hr1]; exact aux_zqr_anti hconv hu (by linarith) s1.le
    have hle : r2 ≤ r1 + Q1 - Q2 := by linarith
    rcases eq_or_lt_of_le hle with h' | h'
    · rw [← h'] at hB; linarith
    · have := aux_zqr_phi_pos hconv hu hQ2 hr2 h'; linarith

lemma aux_zqr_hFun_eq (lam K Q : ℝ) : hFun G lam K Q = G (aux_zqr_aPt G lam K Q) := by
  unfold hFun aux_zqr_aPt
  split_ifs <;> rfl

lemma aux_zqr_aPt_spec (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (lam K : ℝ) {Q : ℝ} (hQ : 0 ≤ Q) :
    G (aux_zqr_aPt G lam K Q + Q) = G (aux_zqr_aPt G lam K Q) := by
  unfold aux_zqr_aPt
  split_ifs with h
  · exact aux_zqr_reorder_spec hc hconv hu lam K h
  · have : Q = 0 := le_antisymm (not_lt.mp h) hQ
    rw [this, add_zero]

lemma aux_zqr_aPt_bounds (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (lam K : ℝ) {Q : ℝ} (hQ : 0 ≤ Q) :
    aux_zqr_aPt G lam K Q ≤ minPt G ∧ minPt G ≤ aux_zqr_aPt G lam K Q + Q := by
  by_cases h : 0 < Q
  · have := aux_zqr_sign hconv hu h (aux_zqr_aPt_spec hc hconv hu lam K hQ)
    exact ⟨this.1.le, this.2.le⟩
  · have hQ0 : Q = 0 := le_antisymm (not_lt.mp h) hQ
    unfold aux_zqr_aPt
    rw [if_neg h, hQ0, add_zero]
    exact ⟨le_rfl, le_rfl⟩

lemma aux_zqr_nest (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (lam K : ℝ) {Q1 Q2 : ℝ} (h1 : 0 ≤ Q1) (h12 : Q1 < Q2) :
    aux_zqr_aPt G lam K Q2 < aux_zqr_aPt G lam K Q1 ∧
      aux_zqr_aPt G lam K Q1 + Q1 < aux_zqr_aPt G lam K Q2 + Q2 := by
  have hQ2 : 0 < Q2 := lt_of_le_of_lt h1 h12
  have s2 := aux_zqr_aPt_spec hc hconv hu lam K hQ2.le
  rcases eq_or_lt_of_le h1 with h | h
  · subst h
    have ha : aux_zqr_aPt G lam K 0 = minPt G := by
      unfold aux_zqr_aPt; rw [if_neg (lt_irrefl 0)]
    rw [ha, add_zero]
    exact aux_zqr_sign hconv hu hQ2 s2
  · exact aux_zqr_zero_nest hconv hu h h12 (aux_zqr_aPt_spec hc hconv hu lam K h1) s2

lemma aux_zqr_H_strict (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (lam K : ℝ) {Q1 Q2 : ℝ} (h1 : 0 ≤ Q1) (h12 : Q1 < Q2) :
    hFun G lam K Q1 < hFun G lam K Q2 := by
  rw [aux_zqr_hFun_eq, aux_zqr_hFun_eq]
  exact aux_zqr_anti hconv hu (aux_zqr_nest hc hconv hu lam K h1 h12).1
    (aux_zqr_aPt_bounds hc hconv hu lam K h1).1

lemma aux_zqr_H_nonpos (lam K : ℝ) {Q : ℝ} (hQ : Q ≤ 0) : hFun G lam K Q = G (minPt G) := by
  unfold hFun; rw [if_neg (not_lt.mpr hQ)]

lemma aux_zqr_H_mono (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (lam K : ℝ) : Monotone (hFun G lam K) := by
  have key : ∀ Q, hFun G lam K Q = hFun G lam K (max Q 0) := by
    intro Q
    rcases le_total Q 0 with h | h
    · rw [max_eq_right h, aux_zqr_H_nonpos lam K h, aux_zqr_H_nonpos lam K le_rfl]
    · rw [max_eq_left h]
  intro x y hxy
  rw [key x, key y]
  have hm : max x 0 ≤ max y 0 := max_le_max hxy le_rfl
  rcases eq_or_lt_of_le hm with h | h
  · rw [h]
  · exact (aux_zqr_H_strict hc hconv hu lam K (le_max_right x 0) h).le

lemma aux_zqr_int_lb {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (h : ∀ x ∈ Set.Icc a b, c ≤ f x) : (b - a) * c ≤ ∫ y in a..b, f y := by
  have := intervalIntegral.integral_mono_on hab intervalIntegrable_const hf h
  simpa [intervalIntegral.integral_const, smul_eq_mul] using this

lemma aux_zqr_int_ub {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (h : ∀ x ∈ Set.Icc a b, f x ≤ c) : ∫ y in a..b, f y ≤ (b - a) * c := by
  have := intervalIntegral.integral_mono_on hab hf intervalIntegrable_const h
  simpa [intervalIntegral.integral_const, smul_eq_mul] using this

lemma aux_zqr_sandwich_core (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) {Q1 Q2 a1 a2 : ℝ}
    (n1 : a2 < a1) (n2 : a1 + Q1 < a2 + Q2) (b1l : a1 ≤ minPt G) (b1r : minPt G ≤ a1 + Q1)
    (s1 : G (a1 + Q1) = G a1) (s2 : G (a2 + Q2) = G a2) :
    (Q2 - Q1) * G a1 ≤ (∫ y in a2..a2 + Q2, G y) - (∫ y in a1..a1 + Q1, G y) ∧
      (∫ y in a2..a2 + Q2, G y) - (∫ y in a1..a1 + Q1, G y) ≤ (Q2 - Q1) * G a2 := by
  have hi : ∀ a b, IntervalIntegrable G volume a b := fun a b => hc.intervalIntegrable a b
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hi a2 a1) (hi a1 (a2 + Q2))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hi a1 (a1 + Q1))
    (hi (a1 + Q1) (a2 + Q2))
  have L1 : (a1 - a2) * G a1 ≤ ∫ y in a2..a1, G y := aux_zqr_int_lb n1.le (hi _ _)
    (fun x hx => aux_zqr_anti_le hconv hu hx.2 b1l)
  have U1 : ∫ y in a2..a1, G y ≤ (a1 - a2) * G a2 := aux_zqr_int_ub n1.le (hi _ _)
    (fun x hx => aux_zqr_anti_le hconv hu hx.1 (hx.2.trans b1l))
  have L2 : (a2 + Q2 - (a1 + Q1)) * G a1 ≤ ∫ y in a1 + Q1..a2 + Q2, G y :=
    aux_zqr_int_lb n2.le (hi _ _) (fun x hx => by
      rw [← s1]; exact aux_zqr_mono_le hconv hu hx.1 b1r)
  have U2 : ∫ y in a1 + Q1..a2 + Q2, G y ≤ (a2 + Q2 - (a1 + Q1)) * G a2 :=
    aux_zqr_int_ub n2.le (hi _ _) (fun x hx => by
      rw [← s2]; exact aux_zqr_mono_le hconv hu hx.2 (b1r.trans hx.1))
  constructor
  · linarith
  · linarith

lemma aux_zqr_sandwich (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (lam K : ℝ) {Q1 Q2 : ℝ} (h1 : 0 ≤ Q1) (h12 : Q1 ≤ Q2) :
    (Q2 - Q1) * hFun G lam K Q1 ≤ aux_zqr_I G lam K Q2 - aux_zqr_I G lam K Q1 ∧
      aux_zqr_I G lam K Q2 - aux_zqr_I G lam K Q1 ≤ (Q2 - Q1) * hFun G lam K Q2 := by
  rcases eq_or_lt_of_le h12 with h | h
  · subst h; simp
  have hQ2 : 0 ≤ Q2 := h1.trans h12
  obtain ⟨n1, n2⟩ := aux_zqr_nest hc hconv hu lam K h1 h
  obtain ⟨b1l, b1r⟩ := aux_zqr_aPt_bounds hc hconv hu lam K h1
  rw [aux_zqr_hFun_eq, aux_zqr_hFun_eq]
  exact aux_zqr_sandwich_core hc hconv hu n1 n2 b1l b1r
    (aux_zqr_aPt_spec hc hconv hu lam K h1) (aux_zqr_aPt_spec hc hconv hu lam K hQ2)

lemma aux_zqr_const_of_bound {D H : ℝ → ℝ} (hD0 : D 0 = 0)
    (hb : ∀ x y, 0 ≤ x → x ≤ y → |D y - D x| ≤ (y - x) * (H y - H x)) {Q : ℝ} (hQ : 0 ≤ Q)
    (hHQ : H 0 ≤ H Q) : D Q = 0 := by
  have key : ∀ n : ℕ, 0 < n → |D Q| ≤ Q / n * (H Q - H 0) := by
    intro n hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    have hδ0 : 0 ≤ Q / n := div_nonneg hQ hnpos.le
    have step : ∀ k : ℕ, |D ((k:ℝ) * (Q / n))| ≤ Q / n * (H ((k:ℝ) * (Q / n)) - H 0) := by
      intro k
      induction k with
      | zero => simp [hD0]
      | succ k ih =>
        have hk0 : (0:ℝ) ≤ (k:ℝ) * (Q / n) := by positivity
        have h1 := hb ((k:ℝ) * (Q / n)) (((k:ℝ) + 1) * (Q / n)) hk0 (by nlinarith)
        have h2 : ((k:ℝ) + 1) * (Q / n) - (k:ℝ) * (Q / n) = Q / n := by ring
        rw [h2] at h1
        push_cast
        have h3 := abs_sub_abs_le_abs_sub (D (((k:ℝ) + 1) * (Q / n))) (D ((k:ℝ) * (Q / n)))
        nlinarith
    have := step n
    have hnδ : (n:ℝ) * (Q / n) = Q := by field_simp
    rw [hnδ] at this
    exact this
  by_contra hne
  have hpos : 0 < |D Q| := abs_pos.mpr hne
  have hM : 0 ≤ Q * (H Q - H 0) := mul_nonneg hQ (by linarith)
  obtain ⟨n, hn⟩ := exists_nat_gt (Q * (H Q - H 0) / |D Q|)
  have hnpos : (0:ℝ) < n := lt_of_le_of_lt (div_nonneg hM hpos.le) hn
  have hn0 : 0 < n := by exact_mod_cast hnpos
  have h1 := key n hn0
  have h2 : Q / n * (H Q - H 0) < |D Q| := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hnpos]
    rw [div_lt_iff₀ hpos] at hn
    linarith
  linarith

lemma aux_zqr_identity (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (lam K : ℝ) {Q : ℝ} (hQ : 0 ≤ Q) :
    aux_zqr_I G lam K Q = ∫ y in (0:ℝ)..Q, hFun G lam K y := by
  have hHm := aux_zqr_H_mono hc hconv hu lam K
  have hint : ∀ a b, IntervalIntegrable (hFun G lam K) volume a b :=
    fun a b => hHm.intervalIntegrable
  let D : ℝ → ℝ := fun Q => aux_zqr_I G lam K Q - ∫ y in (0:ℝ)..Q, hFun G lam K y
  have hD0 : D 0 = 0 := by simp [D, aux_zqr_I]
  have hb : ∀ x y, 0 ≤ x → x ≤ y →
      |D y - D x| ≤ (y - x) * (hFun G lam K y - hFun G lam K x) := by
    intro x y hx hxy
    obtain ⟨l1, u1⟩ := aux_zqr_sandwich hc hconv hu lam K hx hxy
    have e : (∫ t in (0:ℝ)..y, hFun G lam K t) - ∫ t in (0:ℝ)..x, hFun G lam K t =
        ∫ t in x..y, hFun G lam K t :=
      intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)
    have l2 := aux_zqr_int_lb hxy (hint x y) (fun t ht => hHm ht.1)
    have u2 := aux_zqr_int_ub hxy (hint x y) (fun t ht => hHm ht.2)
    simp only [D]
    rw [abs_le]
    constructor <;> linarith
  have := aux_zqr_const_of_bound hD0 hb hQ (hHm hQ)
  simp only [D] at this
  linarith

lemma aux_zqr_H_convex (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (lam K : ℝ) : ConvexOn ℝ (Set.Ici 0) (hFun G lam K) := by
  apply convexOn_of_slope_mono_adjacent (convex_Ici 0)
  intro x y z hx hz hxy hyz
  have hx' : (0:ℝ) ≤ x := hx
  have hy' : 0 ≤ y := hx'.trans hxy.le
  have hz' : 0 ≤ z := hy'.trans hyz.le
  obtain ⟨n1, n2⟩ := aux_zqr_nest hc hconv hu lam K hx' hxy
  obtain ⟨n3, n4⟩ := aux_zqr_nest hc hconv hu lam K hy' hyz
  have sx := aux_zqr_aPt_spec hc hconv hu lam K hx'
  have sy := aux_zqr_aPt_spec hc hconv hu lam K hy'
  have sz := aux_zqr_aPt_spec hc hconv hu lam K hz'
  rw [aux_zqr_hFun_eq, aux_zqr_hFun_eq, aux_zqr_hFun_eq]
  generalize aux_zqr_aPt G lam K x = ax at *
  generalize aux_zqr_aPt G lam K y = ay at *
  generalize aux_zqr_aPt G lam K z = az at *
  have S1 := hconv.slope_mono_adjacent (Set.mem_univ (ax + x)) (Set.mem_univ (az + z)) n2 n4
  have S2 := hconv.slope_mono_adjacent (Set.mem_univ az) (Set.mem_univ ax) n3 n1
  rw [sx, sy, sz] at S1
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at S1
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at S2
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma aux_zqr_A_diff (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (lam K : ℝ) {x y : ℝ} (hxy : x ≤ y) :
    x * (hFun G lam K y - hFun G lam K x) ≤ aFun G lam K y - aFun G lam K x ∧
      aFun G lam K y - aFun G lam K x ≤ y * (hFun G lam K y - hFun G lam K x) := by
  have hHm := aux_zqr_H_mono hc hconv hu lam K
  have hint : ∀ a b, IntervalIntegrable (hFun G lam K) volume a b :=
    fun a b => hHm.intervalIntegrable
  have e : (∫ t in (0:ℝ)..y, hFun G lam K t) - ∫ t in (0:ℝ)..x, hFun G lam K t =
      ∫ t in x..y, hFun G lam K t :=
    intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)
  have l2 := aux_zqr_int_lb hxy (hint x y) (fun t ht => hHm ht.1)
  have u2 := aux_zqr_int_ub hxy (hint x y) (fun t ht => hHm ht.2)
  unfold aFun
  constructor <;> linarith

lemma aux_zqr_A_strict (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (lam K : ℝ) :
    StrictMonoOn (aFun G lam K) (Set.Ici 0) := by
  intro x hx y hy hxy
  have hx' : (0:ℝ) ≤ x := hx
  obtain ⟨m, hxm, hmy⟩ := exists_between hxy
  have hm0 : 0 < m := lt_of_le_of_lt hx' hxm
  have d1 := (aux_zqr_A_diff hc hconv hu lam K hxm.le).1
  have d2 := (aux_zqr_A_diff hc hconv hu lam K hmy.le).1
  have h1 := aux_zqr_H_strict hc hconv hu lam K hx' hxm
  have h2 := aux_zqr_H_strict hc hconv hu lam K hm0.le hmy
  have p1 : 0 < m * (hFun G lam K y - hFun G lam K m) := mul_pos hm0 (by linarith)
  have p2 : 0 ≤ x * (hFun G lam K m - hFun G lam K x) := mul_nonneg hx' (by linarith)
  linarith

lemma aux_zqr_A_convex (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (lam K : ℝ) :
    ConvexOn ℝ (Set.Ici 0) (aFun G lam K) := by
  apply convexOn_of_slope_mono_adjacent (convex_Ici 0)
  intro x y z hx hz hxy hyz
  have hx' : (0:ℝ) ≤ x := hx
  have hy' : 0 ≤ y := hx'.trans hxy.le
  have hHs := (aux_zqr_H_convex hc hconv hu lam K).slope_mono_adjacent hx hz hxy hyz
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at hHs
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have d1 := (aux_zqr_A_diff hc hconv hu lam K hxy.le).2
  have d2 := (aux_zqr_A_diff hc hconv hu lam K hyz.le).1
  have e1 : (aFun G lam K y - aFun G lam K x) * (z - y) ≤
      y * (hFun G lam K y - hFun G lam K x) * (z - y) :=
    mul_le_mul_of_nonneg_right d1 (by linarith)
  have e2 : y * ((hFun G lam K y - hFun G lam K x) * (z - y)) ≤
      y * ((hFun G lam K z - hFun G lam K y) * (y - x)) :=
    mul_le_mul_of_nonneg_left hHs hy'
  have e3 : y * (hFun G lam K z - hFun G lam K y) * (y - x) ≤
      (aFun G lam K z - aFun G lam K y) * (y - x) :=
    mul_le_mul_of_nonneg_right d2 (by linarith)
  nlinarith

lemma aux_zqr_H_cont (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (lam K : ℝ) :
    ContinuousOn (hFun G lam K) (Set.Ici 0) := by
  intro Q hQ
  have hQ' : (0:ℝ) ≤ Q := hQ
  rcases eq_or_lt_of_le hQ' with h | h
  · subst h
    have hH0 : hFun G lam K 0 = G (minPt G) := aux_zqr_H_nonpos lam K le_rfl
    have hup : ∀ q ∈ Set.Ici (0:ℝ), hFun G lam K q ≤ G (minPt G - q) := by
      intro q hq
      have hq' : (0:ℝ) ≤ q := hq
      obtain ⟨bl, br⟩ := aux_zqr_aPt_bounds hc hconv hu lam K hq'
      rw [aux_zqr_hFun_eq]
      exact aux_zqr_anti_le hconv hu (by linarith) bl
    have hlo : ∀ q ∈ Set.Ici (0:ℝ), hFun G lam K 0 ≤ hFun G lam K q := by
      intro q hq
      exact aux_zqr_H_mono hc hconv hu lam K hq
    have ht : Tendsto (fun q => G (minPt G - q)) (𝓝[Set.Ici 0] 0) (𝓝 (hFun G lam K 0)) := by
      have hcc : Continuous (fun q => G (minPt G - q)) :=
        hc.comp (continuous_const.sub continuous_id)
      have h2 := hcc.tendsto 0
      simp only [sub_zero] at h2
      rw [hH0]
      exact h2.mono_left nhdsWithin_le_nhds
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
      (eventually_nhdsWithin_of_forall hlo) (eventually_nhdsWithin_of_forall hup)
  · have hco := (aux_zqr_H_convex hc hconv hu lam K).continuousOn_interior
    rw [interior_Ici] at hco
    exact (hco.continuousAt (isOpen_Ioi.mem_nhds h)).continuousWithinAt

lemma aux_zqr_A_cont (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (lam K : ℝ) :
    ContinuousOn (aFun G lam K) (Set.Ici 0) := by
  have hHm := aux_zqr_H_mono hc hconv hu lam K
  have hprim : Continuous (fun Q => ∫ y in (0:ℝ)..Q, hFun G lam K y) :=
    intervalIntegral.continuous_primitive (fun a b => hHm.intervalIntegrable) 0
  have : aFun G lam K = fun Q => Q * hFun G lam K Q - ∫ y in (0:ℝ)..Q, hFun G lam K y := by
    funext Q; rfl
  rw [this]
  exact (continuousOn_id.mul (aux_zqr_H_cont hc hconv hu lam K)).sub hprim.continuousOn

lemma aux_zqr_exists (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (lam K : ℝ) (hlK : 0 < lam * K) :
    ∃ Q, 0 < Q ∧ aFun G lam K Q = lam * K := by
  have hA0 : aFun G lam K 0 = 0 := by simp [aFun]
  have hc0 : 0 < hFun G lam K 1 - hFun G lam K 0 := by
    have := aux_zqr_H_strict hc hconv hu lam K le_rfl one_pos; linarith
  obtain ⟨Qb, hQb⟩ : ∃ Qb : ℝ, Qb = lam * K / (hFun G lam K 1 - hFun G lam K 0) + 2 := ⟨_, rfl⟩
  have hq : 0 < lam * K / (hFun G lam K 1 - hFun G lam K 0) := div_pos hlK hc0
  have hQb1 : 1 < Qb := by rw [hQb]; linarith
  have hs := (aux_zqr_H_convex hc hconv hu lam K).slope_mono_adjacent (Set.self_mem_Ici)
    (show Qb ∈ Set.Ici (0:ℝ) from Set.mem_Ici.mpr (by linarith)) one_pos hQb1
  rw [div_le_div_iff₀ (by norm_num) (by linarith)] at hs
  have d := (aux_zqr_A_diff hc hconv hu lam K hQb1.le).1
  have hA1 : 0 < aFun G lam K 1 := by
    have := aux_zqr_A_strict hc hconv hu lam K Set.self_mem_Ici
      (show (1:ℝ) ∈ Set.Ici 0 from Set.mem_Ici.mpr zero_le_one) one_pos
    rw [hA0] at this; exact this
  have hkey : (hFun G lam K 1 - hFun G lam K 0) * (Qb - 1) =
      lam * K + (hFun G lam K 1 - hFun G lam K 0) := by
    rw [hQb]; field_simp; ring
  have hbig : lam * K ≤ aFun G lam K Qb := by nlinarith
  have hcont := (aux_zqr_A_cont hc hconv hu lam K).mono
    (Set.Icc_subset_Ici_self : Set.Icc (0:ℝ) Qb ⊆ Set.Ici 0)
  obtain ⟨Q, hQmem, hQ⟩ := intermediate_value_Icc (show (0:ℝ) ≤ Qb by linarith) hcont
    (show lam * K ∈ Set.Icc (aFun G lam K 0) (aFun G lam K Qb) by
      rw [hA0]; exact ⟨hlK.le, hbig⟩)
  refine ⟨Q, ?_, hQ⟩
  rcases eq_or_lt_of_le hQmem.1 with h | h
  · rw [← h, hA0] at hQ; linarith
  · exact h

lemma aux_zqr_optCost_eq (lam K : ℝ) {Q : ℝ} (hQ : 0 < Q) :
    optCost G lam K Q = (lam * K + aux_zqr_I G lam K Q) / Q := by
  unfold optCost qrCost aux_zqr_I aux_zqr_aPt
  rw [if_pos hQ]

lemma aux_zqr_strict_sandwich (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (lam K : ℝ) {Q1 Q2 : ℝ} (h1 : 0 ≤ Q1) (h12 : Q1 < Q2) :
    (Q2 - Q1) * hFun G lam K Q1 < aux_zqr_I G lam K Q2 - aux_zqr_I G lam K Q1 ∧
      aux_zqr_I G lam K Q2 - aux_zqr_I G lam K Q1 < (Q2 - Q1) * hFun G lam K Q2 := by
  obtain ⟨m, hm1, hm2⟩ := exists_between h12
  have hm0 : 0 ≤ m := h1.trans hm1.le
  obtain ⟨l1, u1⟩ := aux_zqr_sandwich hc hconv hu lam K h1 hm1.le
  obtain ⟨l2, u2⟩ := aux_zqr_sandwich hc hconv hu lam K hm0 hm2.le
  have hH1 := aux_zqr_H_strict hc hconv hu lam K h1 hm1
  have hH2 := aux_zqr_H_strict hc hconv hu lam K hm0 hm2
  have p1 : 0 < (Q2 - m) * (hFun G lam K m - hFun G lam K Q1) :=
    mul_pos (by linarith) (by linarith)
  have p2 : 0 < (m - Q1) * (hFun G lam K Q2 - hFun G lam K m) :=
    mul_pos (by linarith) (by linarith)
  constructor <;> linarith

lemma aux_zqr_opt_of_A (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (lam K : ℝ) {Q : ℝ} (hQ : 0 < Q)
    (hA : aFun G lam K Q = lam * K) {Q' : ℝ} (hQ' : 0 < Q') (hne : Q' ≠ Q) :
    optCost G lam K Q < optCost G lam K Q' := by
  have hid := aux_zqr_identity hc hconv hu lam K hQ.le
  have hAeq : aFun G lam K Q = Q * hFun G lam K Q - aux_zqr_I G lam K Q := by
    unfold aFun; rw [hid]
  have hC : optCost G lam K Q = hFun G lam K Q := by
    rw [aux_zqr_optCost_eq lam K hQ, div_eq_iff hQ.ne']
    linarith
  rw [hC, aux_zqr_optCost_eq lam K hQ', lt_div_iff₀ hQ']
  rcases lt_or_gt_of_ne hne with h | h
  · have := (aux_zqr_strict_sandwich hc hconv hu lam K hQ'.le h).2
    linarith
  · have := (aux_zqr_strict_sandwich hc hconv hu lam K hQ.le h).1
    linarith

lemma aux_zqr_char (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (lam K : ℝ) (hlK : 0 < lam * K) :
    (∃! Q : ℝ, IsOptQty G lam K Q) ∧
    (∀ Q : ℝ, 0 < Q → (IsOptQty G lam K Q ↔ aFun G lam K Q = lam * K)) := by
  obtain ⟨Qs, hQs, hAs⟩ := aux_zqr_exists hc hconv hu lam K hlK
  have hopt : ∀ Q, 0 < Q → aFun G lam K Q = lam * K → IsOptQty G lam K Q := by
    intro Q hQ hA
    refine ⟨hQ, fun Q' hQ' => ?_⟩
    rcases eq_or_ne Q' Q with h | h
    · rw [h]
    · exact (aux_zqr_opt_of_A hc hconv hu lam K hQ hA hQ' h).le
  have huniq : ∀ Q, IsOptQty G lam K Q → Q = Qs := by
    intro Q hQ
    by_contra hne
    have h1 := aux_zqr_opt_of_A hc hconv hu lam K hQs hAs hQ.1 hne
    have h2 := hQ.2 Qs hQs
    linarith
  refine ⟨⟨Qs, hopt Qs hQs hAs, huniq⟩, fun Q hQ => ⟨fun h => ?_, hopt Q hQ⟩⟩
  rw [huniq Q h]; exact hAs

lemma aux_zqr_hFun_indep (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (lam K K' : ℝ) : hFun G lam K = hFun G lam K' := by
  funext Q
  unfold hFun
  split_ifs with hQ
  · rw [aux_zqr_zero_unique hconv hu hQ (aux_zqr_reorder_spec hc hconv hu lam K hQ)
      (aux_zqr_reorder_spec hc hconv hu lam K' hQ)]
  · rfl

lemma aux_zqr_aFun_indep (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) (lam K K' : ℝ) : aFun G lam K = aFun G lam K' := by
  funext Q
  unfold aFun
  rw [aux_zqr_hFun_indep hc hconv hu lam K K']

theorem aux_zqr_general (hc : Continuous G) (hconv : ConvexOn ℝ Set.univ G)
    (hu : ∃! y : ℝ, ∀ z, G y ≤ G z) {lam K : ℝ} (hlam : 0 < lam) (hK : 0 < K) :
    StrictMonoOn (aFun G lam K) (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) (aFun G lam K) ∧
    (∃! Q : ℝ, IsOptQty G lam K Q) ∧
    (∀ Q : ℝ, 0 < Q → (IsOptQty G lam K Q ↔ aFun G lam K Q = lam * K)) ∧
    (∀ K' : ℝ, K < K' → ∀ Q Q' : ℝ,
      IsOptQty G lam K Q → IsOptQty G lam K' Q' →
        Q < Q' ∧ reorderPt G lam K' Q' < reorderPt G lam K Q) := by
  have hc1 := aux_zqr_char hc hconv hu lam K (mul_pos hlam hK)
  refine ⟨aux_zqr_A_strict hc hconv hu lam K, aux_zqr_A_convex hc hconv hu lam K, hc1.1,
    hc1.2, ?_⟩
  intro K' hKK' Q Q' hQ hQ'
  have hc2 := aux_zqr_char hc hconv hu lam K' (mul_pos hlam (hK.trans hKK'))
  have hA1 := (hc1.2 Q hQ.1).mp hQ
  have hA2 := (hc2.2 Q' hQ'.1).mp hQ'
  rw [aux_zqr_aFun_indep hc hconv hu lam K' K] at hA2
  have hlKK : lam * K < lam * K' := mul_lt_mul_of_pos_left hKK' hlam
  have hlt : Q < Q' := by
    by_contra hle
    push Not at hle
    have := (aux_zqr_A_strict hc hconv hu lam K).monotoneOn
      (Set.mem_Ici.mpr hQ'.1.le) (Set.mem_Ici.mpr hQ.1.le) hle
    linarith
  refine ⟨hlt, ?_⟩
  exact (aux_zqr_zero_nest hconv hu hQ.1 hlt (aux_zqr_reorder_spec hc hconv hu lam K hQ.1)
    (aux_zqr_reorder_spec hc hconv hu lam K' hQ'.1)).1

end AuxZQR

lemma aux_zqr_nv_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x) μ) (h p y : ℝ) :
    Integrable (fun x => h * max (y - x) 0 + p * max (x - y) 0) μ := by
  have h1 : Integrable (fun x => y - x) μ := (integrable_const y).sub hint
  have h2 : Integrable (fun x => x - y) μ := hint.sub (integrable_const y)
  exact (h1.pos_part.const_mul h).add (h2.pos_part.const_mul p)

lemma aux_zqr_nv_convex {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x) μ) {h p : ℝ} (hh : 0 ≤ h) (hp : 0 ≤ p) :
    ConvexOn ℝ Set.univ (newsvendorCost μ h p) := by
  refine ⟨convex_univ, fun y1 _ y2 _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have I1 := aux_zqr_nv_integrable hint h p y1
  have I2 := aux_zqr_nv_integrable hint h p y2
  have e : a * newsvendorCost μ h p y1 + b * newsvendorCost μ h p y2 =
      ∫ x, (a * (h * max (y1 - x) 0 + p * max (x - y1) 0) +
        b * (h * max (y2 - x) 0 + p * max (x - y2) 0)) ∂μ := by
    unfold newsvendorCost
    rw [integral_add (I1.const_mul a) (I2.const_mul b), integral_const_mul, integral_const_mul]
  rw [e]
  unfold newsvendorCost
  apply integral_mono (aux_zqr_nv_integrable hint h p _) ((I1.const_mul a).add (I2.const_mul b))
  intro x
  have hx : x = a * x + b * x := by rw [← add_mul, hab, one_mul]
  have e1 : max (a * y1 + b * y2 - x) 0 ≤ a * max (y1 - x) 0 + b * max (y2 - x) 0 := by
    apply max_le
    · have := mul_le_mul_of_nonneg_left (le_max_left (y1 - x) 0) ha
      have := mul_le_mul_of_nonneg_left (le_max_left (y2 - x) 0) hb
      nlinarith
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
  have e2 : max (x - (a * y1 + b * y2)) 0 ≤ a * max (x - y1) 0 + b * max (x - y2) 0 := by
    apply max_le
    · have := mul_le_mul_of_nonneg_left (le_max_left (x - y1) 0) ha
      have := mul_le_mul_of_nonneg_left (le_max_left (x - y2) 0) hb
      nlinarith
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
  have f1 := mul_le_mul_of_nonneg_left e1 hh
  have f2 := mul_le_mul_of_nonneg_left e2 hp
  simp only [Pi.add_apply]
  nlinarith

end ZhengQR.EOQHeuristic

open MeasureTheory Filter Topology
open ZhengQR.EOQHeuristic

theorem solution {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) :
    StrictMonoOn (aFun (newsvendorCost μ h p) lam K) (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) (aFun (newsvendorCost μ h p) lam K) ∧
    (∃! Q : ℝ, IsOptQty (newsvendorCost μ h p) lam K Q) ∧
    (∀ Q : ℝ, 0 < Q → (IsOptQty (newsvendorCost μ h p) lam K Q ↔ aFun (newsvendorCost μ h p) lam K Q = lam * K)) ∧
    (∀ K' : ℝ, K < K' → ∀ Q Q' : ℝ,
      IsOptQty (newsvendorCost μ h p) lam K Q → IsOptQty (newsvendorCost μ h p) lam K' Q' →
        Q < Q' ∧ reorderPt (newsvendorCost μ h p) lam K' Q' < reorderPt (newsvendorCost μ h p) lam K Q) := by
  have := hM.isProb
  have hconv := aux_zqr_nv_convex hM.integrable hM.h_pos.le hM.p_pos.le
  have hc : Continuous (newsvendorCost μ h p) := hconv.locallyLipschitz.continuous
  exact aux_zqr_general hc hconv hM.unique_min hM.lam_pos hK
