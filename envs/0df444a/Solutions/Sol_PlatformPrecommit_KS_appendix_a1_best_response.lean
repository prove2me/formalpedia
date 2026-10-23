-- Prove2me | solution 1 for PlatformPrecommit.KS.appendix_a1_best_response
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T12:18:56.110517+00:00
-- url     : https://prove2.me/submissions/c4eef4ea-b6f3-453b-87b6-319deca46c76

import Mathlib
import Definitions.Def_PlatformPrecommit_KS_Setting

namespace KSAux

/-- Capacity fixed-point condition for one platform: `m = min y ((L - c n)/(s+2))`. -/
def Fx (L s c y m n : ℝ) : Prop :=
  m ≤ y ∧ (s + 2) * m + c * n ≤ L ∧ (m = y ∨ (s + 2) * m + c * n = L)

/-- Quantity-game profit `x (L - s x - c y)`. -/
def ff (L s c x y : ℝ) : ℝ := x * (L - s * x - c * y)

structure Par (L s c : ℝ) : Prop where
  hL : 0 < L
  hs : 2 ≤ s
  hc : 0 ≤ c
  hcs : c ^ 2 + s + 2 ≤ s ^ 2

section Abstract
variable {L s c : ℝ}

lemma Par.c_lt (P : Par L s c) : c < s + 2 := by
  have := P.hcs; have := P.hs; have := P.hc
  nlinarith

lemma Par.c_lt' (P : Par L s c) : c < s := by
  have := P.hcs; have := P.hs; have := P.hc
  nlinarith

lemma cu_lt (P : Par L s c) {u w : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w)
    (h : (s + 2) * u + c * w ≤ L) : c * u < L := by
  have hc := P.hc; have hcl := P.c_lt; have hL := P.hL
  have h1 : (s + 2) * u ≤ L := by nlinarith
  have h2 : (s + 2) * (c * u) ≤ (s + 2) * L := by nlinarith
  rcases eq_or_lt_of_le hu with hu0 | hu0
  · subst hu0; simp; exact hL
  · have : c * u < (s + 2) * u := by nlinarith
    linarith

lemma lb_of_eq (P : Par L s c) {a b : ℝ} (h1 : (s + 2) * b + c * a = L)
    (h2 : (s + 2) * a + c * b ≤ L) : L ≤ (s + 2 + c) * b := by
  have hcl := P.c_lt
  have hc := P.hc
  have key : ((s + 2) ^ 2 - c ^ 2) * b ≥ (s + 2 - c) * L := by
    nlinarith [mul_le_mul_of_nonneg_left h2 hc]
  have hpos : 0 < s + 2 - c := by linarith
  by_contra hh
  push_neg at hh
  nlinarith [mul_lt_mul_of_pos_left hh hpos]

lemma cross (P : Par L s c) {u v : ℝ} (h1 : (s + 2 + c) * u ≤ L)
    (h2 : (s + 2) * v + c * u ≤ L) : (s + 2) * u + c * v ≤ L := by
  have hcl := P.c_lt
  have hc := P.hc
  have hs := P.hs
  have hpos : 0 ≤ s + 2 - c := by linarith
  have h3 : (s + 2) * ((s + 2) * u + c * v) ≤ (s + 2) * L := by
    nlinarith [mul_le_mul_of_nonneg_left h2 hc, mul_le_mul_of_nonneg_left h1 hpos]
  exact le_of_mul_le_mul_left h3 (by linarith)

lemma exists_fix (P : Par L s c) {y1 y2 : ℝ} (h1 : 0 ≤ y1) (h2 : 0 ≤ y2) :
    ∃ m1 m2 : ℝ, 0 ≤ m1 ∧ 0 ≤ m2 ∧ Fx L s c y1 m1 m2 ∧ Fx L s c y2 m2 m1 := by
  have hL := P.hL; have hs := P.hs; have hc := P.hc; have hcl := P.c_lt
  have hd : 0 < s + 2 + c := by linarith
  have hd2 : 0 < s + 2 := by linarith
  have hpos : 0 ≤ s + 2 - c := by linarith
  by_cases C1 : L ≤ (s + 2 + c) * y1 ∧ L ≤ (s + 2 + c) * y2
  · set mB := L / (s + 2 + c) with hmB
    have hmB' : (s + 2 + c) * mB = L := by rw [hmB]; field_simp
    have hmBpos : 0 < mB := div_pos hL hd
    refine ⟨mB, mB, hmBpos.le, hmBpos.le, ⟨?_, ?_, Or.inr ?_⟩, ⟨?_, ?_, Or.inr ?_⟩⟩
    · exact le_of_mul_le_mul_left (by linarith [C1.1]) hd
    · linear_combination hmB'
    · linear_combination hmB'
    · exact le_of_mul_le_mul_left (by linarith [C1.2]) hd
    · linear_combination hmB'
    · linear_combination hmB'
  by_cases C2 : (s + 2 + c) * y1 < L ∧ L ≤ (s + 2) * y2 + c * y1
  · set m2 := (L - c * y1) / (s + 2) with hm2d
    have hm2 : (s + 2) * m2 = L - c * y1 := by rw [hm2d]; field_simp
    have hcy : c * y1 ≤ L := by nlinarith [C2.1]
    refine ⟨y1, m2, h1, ?_, ⟨le_rfl, ?_, Or.inl rfl⟩, ⟨?_, ?_, Or.inr ?_⟩⟩
    · exact div_nonneg (by linarith) hd2.le
    · have e : (s + 2) * ((s + 2) * y1 + c * m2) = (s + 2) ^ 2 * y1 + c * (L - c * y1) := by
        linear_combination c * hm2
      have : (s + 2) * ((s + 2) * y1 + c * m2) ≤ (s + 2) * L := by
        rw [e]; nlinarith [mul_le_mul_of_nonneg_left C2.1.le hpos]
      exact le_of_mul_le_mul_left this hd2
    · exact le_of_mul_le_mul_left (by linarith [C2.2]) hd2
    · linarith
    · linarith
  by_cases C3 : (s + 2 + c) * y2 < L ∧ L ≤ (s + 2) * y1 + c * y2
  · set m1 := (L - c * y2) / (s + 2) with hm1d
    have hm1 : (s + 2) * m1 = L - c * y2 := by rw [hm1d]; field_simp
    have hcy : c * y2 ≤ L := by nlinarith [C3.1]
    refine ⟨m1, y2, ?_, h2, ⟨?_, ?_, Or.inr ?_⟩, ⟨le_rfl, ?_, Or.inl rfl⟩⟩
    · exact div_nonneg (by linarith) hd2.le
    · exact le_of_mul_le_mul_left (by linarith [C3.2]) hd2
    · linarith
    · linarith
    · have e : (s + 2) * ((s + 2) * y2 + c * m1) = (s + 2) ^ 2 * y2 + c * (L - c * y2) := by
        linear_combination c * hm1
      have : (s + 2) * ((s + 2) * y2 + c * m1) ≤ (s + 2) * L := by
        rw [e]; nlinarith [mul_le_mul_of_nonneg_left C3.1.le hpos]
      exact le_of_mul_le_mul_left this hd2
  -- Case 4: both capacities bind
  have AB : (s + 2) * y1 + c * y2 ≤ L ∧ (s + 2) * y2 + c * y1 ≤ L := by
    by_cases h : (s + 2 + c) * y1 < L
    · have B : (s + 2) * y2 + c * y1 < L := by
        by_contra hb; push_neg at hb; exact C2 ⟨h, hb⟩
      by_cases h' : (s + 2 + c) * y2 < L
      · have A : (s + 2) * y1 + c * y2 < L := by
          by_contra ha; push_neg at ha; exact C3 ⟨h', ha⟩
        exact ⟨A.le, B.le⟩
      · exact ⟨cross P h.le B.le, B.le⟩
    · push_neg at h
      have h' : (s + 2 + c) * y2 < L := by
        by_contra hb; push_neg at hb; exact C1 ⟨h, hb⟩
      have A : (s + 2) * y1 + c * y2 < L := by
        by_contra ha; push_neg at ha; exact C3 ⟨h', ha⟩
      exact ⟨A.le, cross P h'.le A.le⟩
  exact ⟨y1, y2, h1, h2, ⟨le_rfl, AB.1, Or.inl rfl⟩, ⟨le_rfl, AB.2, Or.inl rfl⟩⟩

lemma pin (P : Par L s c) {Y a b B : ℝ} (hF : Fx L s c Y a b) (hb : b ≤ B)
    (h : (s + 2) * Y + c * B ≤ L) : a = Y := by
  obtain ⟨h1, h2, h3⟩ := hF
  have hc := P.hc
  rcases h3 with h3 | h3
  · exact h3
  · by_contra hne
    have hlt : a < Y := lt_of_le_of_ne h1 hne
    have hs := P.hs
    nlinarith [mul_le_mul_of_nonneg_left hb hc, mul_lt_mul_of_pos_left hlt (by linarith : (0:ℝ) < s + 2)]

lemma star (P : Par L s c) {Q m1 m2 : ℝ}
    (D : ∀ v, 0 < v → ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ Fx L s c v a b ∧ Fx L s c Q b a ∧
      ff L s c a b ≤ ff L s c m1 m2) :
    ∀ v, 0 < v → (s + 2) * v + c * Q ≤ L → ff L s c v Q ≤ ff L s c m1 m2 := by
  intro v hv hvQ
  obtain ⟨a, b, ha, hb, Fa, Fb, hle⟩ := D v hv
  have hav : a = v := pin P Fa Fb.1 hvQ
  subst hav
  have hc := P.hc
  have : ff L s c a Q ≤ ff L s c a b := by
    unfold ff; nlinarith [mul_le_mul_of_nonneg_left Fb.1 hc, mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left Fb.1 hc) ha]
  linarith

lemma devC (P : Par L s c) {Q m1 m2 : ℝ}
    (D : ∀ v, 0 < v → ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ Fx L s c v a b ∧ Fx L s c Q b a ∧
      ff L s c a b ≤ ff L s c m1 m2) :
    ∀ v, 0 < v → (s + 2 + c) * v < L →
      v * ((s + 2 - c) * L - (s * (s + 2) - c ^ 2) * v) ≤ (s + 2) * ff L s c m1 m2 := by
  intro v hv hvL
  obtain ⟨a, b, ha, hb, Fa, Fb, hle⟩ := D v hv
  have hc := P.hc
  have hav : a = v := by
    obtain ⟨h1, h2, h3⟩ := Fa
    rcases h3 with h3 | h3
    · exact h3
    · exfalso
      have := lb_of_eq P h3 Fb.2.1
      rcases eq_or_lt_of_le h1 with h | h
      · subst h; linarith
      · have hd : 0 < s + 2 + c := by linarith [P.hs]
        nlinarith [mul_lt_mul_of_pos_left h hd]
  subst hav
  have hmid := Fb.2.1
  have hcv : 0 ≤ c * a := mul_nonneg hc ha
  have : a * ((s + 2 - c) * L - (s * (s + 2) - c ^ 2) * a) ≤ (s + 2) * ff L s c a b := by
    unfold ff
    nlinarith [mul_le_mul_of_nonneg_left hmid hcv]
  have hs2 : 0 ≤ s + 2 := by linarith [P.hs]
  nlinarith [mul_le_mul_of_nonneg_left hle hs2]

lemma best_resp_eq (P : Par L s c) {z w : ℝ} (hw : 0 ≤ w)
    (H : ∀ x, 0 ≤ x → ff L s c x w ≤ ff L s c z w) (hpos : 0 < L - c * w) :
    2 * s * z + c * w = L := by
  have hs := P.hs
  set R := (L - c * w) / (2 * s) with hRd
  have hR : 2 * s * R = L - c * w := by rw [hRd]; field_simp
  have hR0 : 0 ≤ R := div_nonneg hpos.le (by linarith)
  have h := H R hR0
  unfold ff at h
  have e : R * (L - s * R - c * w) - z * (L - s * z - c * w) = s * (z - R) ^ 2 := by
    linear_combination (z - R) * hR
  have : s * (z - R) ^ 2 ≤ 0 := by linarith
  have hz : (z - R) ^ 2 = 0 := by
    have := sq_nonneg (z - R)
    have hs0 : 0 < s := by linarith
    nlinarith
  have : z = R := by nlinarith [pow_eq_zero_iff (n := 2) (a := z - R) two_ne_zero |>.mp hz]
  subst this
  linarith

lemma spe_core (P : Par L s c) {q1 q2 m1 m2 : ℝ}
    (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (F1 : Fx L s c q1 m1 m2) (F2 : Fx L s c q2 m2 m1)
    (D1 : ∀ v, 0 < v → ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ Fx L s c v a b ∧ Fx L s c q2 b a ∧
      ff L s c a b ≤ ff L s c m1 m2)
    (D2 : ∀ v, 0 < v → ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ Fx L s c v a b ∧ Fx L s c q1 b a ∧
      ff L s c a b ≤ ff L s c m2 m1) :
    (2 * s + c) * m1 = L ∧ (2 * s + c) * m2 = L := by
  have S1 := star P D1
  have S2 := star P D2
  have hL := P.hL; have hs := P.hs; have hc := P.hc; have hcl := P.c_lt; have hcl' := P.c_lt'
  have hcs := P.hcs
  by_cases hs2 : s = 2
  · subst hs2
    have hc0 : c = 0 := by nlinarith
    subst hc0
    have k1 := S1 (L / 4) (by linarith) (by linarith)
    have k2 := S2 (L / 4) (by linarith) (by linarith)
    unfold ff at k1 k2
    constructor <;> nlinarith [sq_nonneg (m1 - L / 4), sq_nonneg (m2 - L / 4)]
  have hs2' : 2 < s := lt_of_le_of_ne hs (Ne.symm hs2)
  -- Cournot best-response step against a binding rival
  have brA : ∀ (x y : ℝ), 0 ≤ x → 0 ≤ y → (s + 2) * y + c * x ≤ L →
      (s + 2) * x + c * y ≤ L →
      (∀ v, 0 < v → (s + 2) * v + c * x ≤ L → ff L s c v x ≤ ff L s c y x) →
      2 * s * y + c * x = L := by
    intro x y hx hy hxy hxy' Sx
    have hcx : c * x < L := cu_lt P hx hy hxy'
    set R := (L - c * x) / (2 * s) with hRd
    have hR : 2 * s * R = L - c * x := by rw [hRd]; field_simp
    have hRp : 0 < R := div_pos (by linarith) (by linarith)
    have hRL : (s + 2) * R + c * x ≤ L := by nlinarith
    have h := Sx R hRp hRL
    unfold ff at h
    have e : R * (L - s * R - c * x) - y * (L - s * y - c * x) = s * (y - R) ^ 2 := by
      linear_combination (y - R) * hR
    have h' : s * (y - R) ^ 2 ≤ 0 := by linarith
    have : (y - R) ^ 2 = 0 := by nlinarith [sq_nonneg (y - R)]
    have : y = R := by nlinarith [pow_eq_zero_iff (n := 2) (a := y - R) two_ne_zero |>.mp this]
    subst this; linarith
  obtain ⟨a1, b1, e1⟩ := F1
  obtain ⟨a2, b2, e2⟩ := F2
  rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
  · -- both bind
    subst e1; subst e2
    have r1 := brA m2 m1 hm2 hm1 b1 b2 S1
    have r2 := brA m1 m2 hm1 hm2 b2 b1 S2
    have : m1 = m2 := by
      have : (2 * s - c) * (m1 - m2) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    subst this
    constructor <;> linarith
  · -- firm 1 binds, firm 2 does not
    subst e1
    have r2 := brA m1 m2 hm1 hm2 b2 b1 S2
    have hm2p : 0 < m2 := by
      have := cu_lt P hm1 hm2 b1
      nlinarith
    exfalso
    have : (s - 2) * m2 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact hs2 (by linarith)
    · linarith
  · subst e2
    have r1 := brA m2 m1 hm2 hm1 b1 b2 S1
    have hm1p : 0 < m1 := by
      have := cu_lt P hm2 hm1 b2
      nlinarith
    exfalso
    have : (s - 2) * m1 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact hs2 (by linarith)
    · linarith
  · -- neither binds: profitable downward deviation
    exfalso
    have heq : m1 = m2 := by
      have : (s + 2 - c) * (m1 - m2) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    subst heq
    set m := m1
    have hmL : (s + 2 + c) * m = L := by linarith
    have hmp : 0 < m := by
      by_contra h; push_neg at h
      have : m = 0 := le_antisymm h hm1
      rw [this] at hmL; linarith
    set A := (s + 2 - c) * L with hA
    set B := s * (s + 2) - c ^ 2 with hB
    have hBp : 0 < B := by rw [hB]; nlinarith
    have hAp : 0 < A := by rw [hA]; nlinarith
    have hc4 : c ^ 2 < (s + 2) * (s - 2) := by nlinarith
    have hA2 : A < 2 * B * m := by
      rw [hA, hB, ← hmL]; nlinarith [mul_lt_mul_of_pos_right hc4 hmp]
    set v := (A + 2 * B * m) / (4 * B) with hvd
    have hv : 4 * B * v = A + 2 * B * m := by rw [hvd]; field_simp
    have hvp : 0 < v := div_pos (by nlinarith) (by linarith)
    have hvm : v < m := by nlinarith
    have hvL : (s + 2 + c) * v < L := by
      rw [← hmL]; exact mul_lt_mul_of_pos_left hvm (by linarith)
    have k := devC P D1 v hvp hvL
    have e : (s + 2) * ff L s c m m = m * (A - B * m) := by
      unfold ff; rw [hA, hB]; linear_combination (-(m * c)) * hmL
    rw [e] at k
    have h1 : v - m < 0 := by linarith
    have h2 : A - B * (v + m) < 0 := by nlinarith
    have : 0 < (v - m) * (A - B * (v + m)) := mul_pos_of_neg_of_neg h1 h2
    nlinarith

lemma qne_core (P : Par L s c) {z1 z2 : ℝ} (h1 : 0 ≤ z1) (h2 : 0 ≤ z2)
    (H1 : ∀ x, 0 ≤ x → ff L s c x z2 ≤ ff L s c z1 z2)
    (H2 : ∀ x, 0 ≤ x → ff L s c x z1 ≤ ff L s c z2 z1) :
    (2 * s + c) * z1 = L ∧ (2 * s + c) * z2 = L := by
  have hL := P.hL; have hs := P.hs; have hc := P.hc; have hcl' := P.c_lt'
  have zero : ∀ z w, 0 ≤ z → (∀ x, 0 ≤ x → ff L s c x w ≤ ff L s c z w) →
      L - c * w ≤ 0 → z = 0 := by
    intro z w hz H hneg
    have h0 := H 0 le_rfl
    unfold ff at h0
    have : s * z ^ 2 ≤ 0 := by nlinarith [mul_nonneg hz (by linarith : 0 ≤ -(L - c * w))]
    nlinarith [sq_nonneg z]
  have pos : ∀ z w, 0 ≤ z → 0 ≤ w → (∀ x, 0 ≤ x → ff L s c x w ≤ ff L s c z w) →
      (∀ x, 0 ≤ x → ff L s c x z ≤ ff L s c w z) → 0 < L - c * w := by
    intro z w hz hw Hz Hw
    by_contra hneg; push_neg at hneg
    have hz0 := zero z w hz Hz hneg
    subst hz0
    have := best_resp_eq P le_rfl Hw (by simp; exact hL)
    have hwp : 0 < w := by nlinarith
    nlinarith
  have p2 := pos z1 z2 h1 h2 H1 H2
  have p1 := pos z2 z1 h2 h1 H2 H1
  have r1 := best_resp_eq P h2 H1 p2
  have r2 := best_resp_eq P h1 H2 p1
  have : z1 = z2 := by
    have : (2 * s - c) * (z1 - z2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  subst this
  constructor <;> linarith

lemma quad (K y m z : ℝ) (hm0 : 0 ≤ m) (hmy : m ≤ y) (hzy : z ≤ y) (hzK : 4 * z ≤ K)
    (hor : z = y ∨ 4 * z = K) :
    (K - 2 * m) * m ≤ (K - 2 * z) * z ∧ ((K - 2 * m) * m = (K - 2 * z) * z → m = z) := by
  rcases hor with h | h
  · subst h
    constructor
    · nlinarith [mul_nonneg (by linarith : 0 ≤ z - m) (by linarith : 0 ≤ K - 2 * z - 2 * m)]
    · intro he
      have : (z - m) * (K - 2 * z - 2 * m) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
  · constructor
    · nlinarith [sq_nonneg (m - z)]
    · intro he
      have : (m - z) ^ 2 = 0 := by nlinarith
      have := pow_eq_zero_iff (n := 2) (a := m - z) two_ne_zero |>.mp this
      linarith

end Abstract

section Glue
open PlatformPrecommit.KS

lemma r0 : rival 0 = 1 := rfl
lemma r1 : rival 1 = 0 := rfl

lemma rival_rival (i : Fin 2) : rival (rival i) = i := by fin_cases i <;> rfl
lemma rival_ne (i : Fin 2) : rival i ≠ i := by fin_cases i <;> decide

noncomputable def Lm (M : Model) : ℝ := M.Ω / (1 - M.γ)
noncomputable def sm (M : Model) : ℝ := 1 / (1 - M.γ ^ 2) + 1 / (1 - M.β ^ 2)
noncomputable def cm (M : Model) : ℝ := M.γ / (1 - M.γ ^ 2) + M.β / (1 - M.β ^ 2)

lemma par_of (M : Model) (hM : M.Standing) : Par (Lm M) (sm M) (cm M) := by
  obtain ⟨hΩ, hγ0, hγ1, hβ0, hβ1⟩ := hM
  have hg : 0 < 1 - M.γ ^ 2 := by nlinarith
  have hb : 0 < 1 - M.β ^ 2 := by nlinarith
  set a := 1 / (1 - M.γ ^ 2) with ha_def
  set b := 1 / (1 - M.β ^ 2) with hb_def
  have ha : a * (1 - M.γ ^ 2) = 1 := by rw [ha_def]; field_simp
  have hb' : b * (1 - M.β ^ 2) = 1 := by rw [hb_def]; field_simp
  have ha0 : 0 < a := div_pos one_pos hg
  have hb0 : 0 < b := div_pos one_pos hb
  have ha1 : 1 ≤ a := by nlinarith [mul_nonneg ha0.le (sq_nonneg M.γ)]
  have hb1 : 1 ≤ b := by nlinarith [mul_nonneg hb0.le (sq_nonneg M.β)]
  have hcm : cm M = a * M.γ + b * M.β := by unfold cm; rw [ha_def, hb_def]; ring
  have hsm : sm M = a + b := by unfold sm; rfl
  refine ⟨div_pos hΩ (by linarith), ?_, ?_, ?_⟩
  · rw [hsm]; linarith
  · rw [hcm]; positivity
  · rw [hcm, hsm]
    have e : (a + b) ^ 2 - (a * M.γ + b * M.β) ^ 2 - (a + b) - 2 =
        2 * (a * b * (1 - M.γ * M.β)) - 2 := by
      linear_combination a * ha + b * hb'
    have key : (1 - M.γ ^ 2) * (1 - M.β ^ 2) ≤ 1 - M.γ * M.β := by
      have hgb : M.γ * M.β ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (M.γ - M.β), mul_nonneg (mul_nonneg hγ0 hβ0) (by linarith : 0 ≤ 1 - M.γ * M.β)]
    have hab1 : a * b * ((1 - M.γ ^ 2) * (1 - M.β ^ 2)) = 1 := by
      linear_combination (b * (1 - M.β ^ 2)) * ha + hb'
    have := mul_le_mul_of_nonneg_left key (mul_nonneg ha0.le hb0.le)
    nlinarith

lemma hden (M : Model) (hM : M.Standing) :
    (1 - M.γ ^ 2) ≠ 0 ∧ (1 - M.β ^ 2) ≠ 0 ∧ (1 - M.γ) ≠ 0 := by
  obtain ⟨hΩ, hγ0, hγ1, hβ0, hβ1⟩ := hM
  refine ⟨?_, ?_, ?_⟩
  · have : 0 < 1 - M.γ ^ 2 := by nlinarith
    exact this.ne'
  · have : 0 < 1 - M.β ^ 2 := by nlinarith
    exact this.ne'
  · have : 0 < 1 - M.γ := by linarith
    exact this.ne'

lemma I1 (M : Model) (hM : M.Standing) (z : Fin 2 → ℝ) (i : Fin 2) :
    M.Ω - M.qPrice z i + M.γ * M.qPrice z (rival i) = z i := by
  obtain ⟨h1, h2, h3⟩ := hden M hM
  unfold Model.qPrice; rw [rival_rival]; field_simp; ring

lemma I2 (M : Model) (hM : M.Standing) (z : Fin 2 → ℝ) (i : Fin 2) :
    M.qWage z i - M.β * M.qWage z (rival i) = z i := by
  obtain ⟨h1, h2, h3⟩ := hden M hM
  unfold Model.qWage; rw [rival_rival]; field_simp; ring

lemma I3 (M : Model) (hM : M.Standing) (z : Fin 2 → ℝ) (i : Fin 2) :
    M.qPrice z i - M.qWage z i = Lm M - sm M * z i - cm M * z (rival i) := by
  obtain ⟨h1, h2, h3⟩ := hden M hM
  have h4 : (1 + M.γ) ≠ 0 := by
    obtain ⟨hΩ, hγ0, hγ1, hβ0, hβ1⟩ := hM; have : 0 < 1 + M.γ := by linarith
    exact this.ne'
  have e : (1 - M.γ ^ 2) = (1 - M.γ) * (1 + M.γ) := by ring
  unfold Model.qPrice Model.qWage Lm sm cm
  rw [e]
  field_simp
  ring

lemma K_eq (M : Model) (hM : M.Standing) (z : Fin 2 → ℝ) (i : Fin 2) :
    M.Ω + M.γ * M.qPrice z (rival i) - M.β * M.qWage z (rival i) =
      Lm M - (sm M - 2) * z i - cm M * z (rival i) := by
  have a := I1 M hM z i
  have b := I2 M hM z i
  have c := I3 M hM z i
  linarith

/-- residual market of platform `i` given the rival's price and wage. -/
def Kf (M : Model) (pw : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (i : Fin 2) : ℝ :=
  M.Ω + M.γ * pw.1 (rival i) - M.β * pw.2 (rival i)

lemma prof_le (M : Model) (y : Fin 2 → ℝ) (pw : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (i : Fin 2)
    (hy : 0 ≤ y i) :
    0 ≤ M.ksMatch y pw i ∧ M.ksMatch y pw i ≤ y i ∧
    M.ksProfit y pw i ≤ (Kf M pw i - 2 * M.ksMatch y pw i) * M.ksMatch y pw i ∧
    (0 < M.ksMatch y pw i →
      M.ksProfit y pw i = (Kf M pw i - 2 * M.ksMatch y pw i) * M.ksMatch y pw i →
      pw.1 i = M.Ω + M.γ * pw.1 (rival i) - M.ksMatch y pw i ∧
      pw.2 i = M.ksMatch y pw i + M.β * pw.2 (rival i)) := by
  have hdef : M.ksMatch y pw i = min (min (max (M.Ω - pw.1 i + M.γ * pw.1 (rival i)) 0)
      (max (pw.2 i - M.β * pw.2 (rival i)) 0)) (y i) := rfl
  have hprof : M.ksProfit y pw i = (pw.1 i - pw.2 i) * M.ksMatch y pw i := rfl
  set m := M.ksMatch y pw i with hm
  have hm0 : 0 ≤ m := by
    rw [hdef]; exact le_min (le_min (le_max_right _ _) (le_max_right _ _)) hy
  have hmy : m ≤ y i := by rw [hdef]; exact min_le_right _ _
  have hmd : m ≤ max (M.Ω - pw.1 i + M.γ * pw.1 (rival i)) 0 := by
    rw [hdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hms : m ≤ max (pw.2 i - M.β * pw.2 (rival i)) 0 := by
    rw [hdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have pos : 0 < m → m ≤ M.Ω - pw.1 i + M.γ * pw.1 (rival i) ∧
      m ≤ pw.2 i - M.β * pw.2 (rival i) := by
    intro hp
    constructor
    · rcases le_max_iff.mp hmd with h | h
      · exact h
      · linarith
    · rcases le_max_iff.mp hms with h | h
      · exact h
      · linarith
  refine ⟨hm0, hmy, ?_, ?_⟩
  · rw [hprof]
    rcases eq_or_lt_of_le hm0 with h | h
    · rw [← h]; simp
    · obtain ⟨d, s⟩ := pos h
      unfold Kf
      exact mul_le_mul_of_nonneg_right (by linarith) hm0
  · intro hp he
    obtain ⟨d, s⟩ := pos hp
    rw [hprof] at he
    unfold Kf at he
    have : pw.1 i - pw.2 i = M.Ω + M.γ * pw.1 (rival i) - M.β * pw.2 (rival i) - 2 * m :=
      mul_right_cancel₀ hp.ne' he
    constructor <;> linarith

lemma dev_prof (M : Model) (y : Fin 2 → ℝ) (pw : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (i : Fin 2)
    (z : ℝ) (hz0 : 0 ≤ z) (hzy : z ≤ y i) :
    M.ksProfit y (Function.update pw.1 i (M.Ω + M.γ * pw.1 (rival i) - z),
      Function.update pw.2 i (z + M.β * pw.2 (rival i))) i = (Kf M pw i - 2 * z) * z := by
  unfold Model.ksProfit Model.ksMatch Model.demand Model.supply Kf
  simp only [Function.update_self, Function.update_of_ne (rival_ne i)]
  have e1 : M.Ω - (M.Ω + M.γ * pw.1 (rival i) - z) + M.γ * pw.1 (rival i) = z := by ring
  have e2 : z + M.β * pw.2 (rival i) - M.β * pw.2 (rival i) = z := by ring
  rw [e1, e2, max_eq_left hz0, min_self, min_eq_left hzy]
  ring

def FixM (M : Model) (y m : Fin 2 → ℝ) : Prop :=
  ∀ i, Fx (Lm M) (sm M) (cm M) (y i) (m i) (m (rival i))

lemma ne_of_fix (M : Model) (hM : M.Standing) (y m : Fin 2 → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hm : ∀ i, 0 ≤ m i) (hF : FixM M y m) :
    (∀ i, M.ksMatch y (M.qPrice m, M.qWage m) i = m i) ∧
    (∀ i, M.ksProfit y (M.qPrice m, M.qWage m) i =
      ff (Lm M) (sm M) (cm M) (m i) (m (rival i))) ∧
    M.IsSubNE y (M.qPrice m, M.qWage m) ∧
    (∀ i, 0 < y i → 0 < M.ksProfit y (M.qPrice m, M.qWage m) i) := by
  have P := par_of M hM
  have hmatch : ∀ i, M.ksMatch y (M.qPrice m, M.qWage m) i = m i := by
    intro i
    unfold Model.ksMatch Model.demand Model.supply
    simp only
    rw [I1 M hM m i, I2 M hM m i, max_eq_left (hm i), min_self, min_eq_left (hF i).1]
  have hprof : ∀ i, M.ksProfit y (M.qPrice m, M.qWage m) i =
      ff (Lm M) (sm M) (cm M) (m i) (m (rival i)) := by
    intro i
    unfold Model.ksProfit; rw [hmatch i]; simp only; rw [I3 M hM m i]; unfold ff; ring
  refine ⟨hmatch, hprof, ?_, ?_⟩
  · intro i a b
    obtain ⟨h0, h1, h2, -⟩ := prof_le M y
      (Function.update (M.qPrice m, M.qWage m).1 i a,
        Function.update (M.qPrice m, M.qWage m).2 i b) i (hy i)
    have hK : Kf M (Function.update (M.qPrice m, M.qWage m).1 i a,
        Function.update (M.qPrice m, M.qWage m).2 i b) i =
        Lm M - (sm M - 2) * m i - cm M * m (rival i) := by
      unfold Kf
      simp only [Function.update_of_ne (rival_ne i)]
      exact K_eq M hM m i
    rw [hK] at h2
    obtain ⟨F1, F2, F3⟩ := hF i
    have q := (quad (Lm M - (sm M - 2) * m i - cm M * m (rival i)) (y i) _ (m i) h0 h1 F1
      (by linarith) (by rcases F3 with h | h
                        · left; exact h
                        · right; linarith)).1
    calc _ ≤ _ := h2
      _ ≤ _ := q
      _ = _ := by rw [hprof i]; unfold ff; ring
  · intro i hyi
    rw [hprof i]
    obtain ⟨F1, F2, F3⟩ := hF i
    have hmi : 0 < m i := by
      rcases F3 with h | h
      · rw [h]; exact hyi
      · have h' := (hF (rival i)).2.1
        rw [rival_rival] at h'
        have := cu_lt P (hm (rival i)) (hm i) h'
        nlinarith [P.hs]
    unfold ff
    have hs := P.hs
    nlinarith

lemma br_step (M : Model) (y : Fin 2 → ℝ) (pw : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (i : Fin 2)
    (hy : 0 ≤ y i) (hNE : M.IsSubNE y pw) (hpos : 0 < M.ksProfit y pw i) :
    0 < M.ksMatch y pw i ∧ M.ksMatch y pw i ≤ y i ∧ 4 * M.ksMatch y pw i ≤ Kf M pw i ∧
    (M.ksMatch y pw i = y i ∨ 4 * M.ksMatch y pw i = Kf M pw i) ∧
    pw.1 i = M.Ω + M.γ * pw.1 (rival i) - M.ksMatch y pw i ∧
    pw.2 i = M.ksMatch y pw i + M.β * pw.2 (rival i) ∧
    M.ksProfit y pw i = (Kf M pw i - 2 * M.ksMatch y pw i) * M.ksMatch y pw i := by
  obtain ⟨h0, h1, h2, h3⟩ := prof_le M y pw i hy
  set m := M.ksMatch y pw i with hmdef
  set K := Kf M pw i with hKdef
  have hm : 0 < m := by
    rcases eq_or_lt_of_le h0 with h | h
    · rw [← h] at h2; simp at h2; linarith
    · exact h
  have hK : 0 < K := by nlinarith
  set z := min (y i) (K / 4) with hz
  have hz0 : 0 < z := lt_min (lt_of_lt_of_le hm h1) (by linarith)
  have hzy : z ≤ y i := min_le_left _ _
  have hzK : 4 * z ≤ K := by have := min_le_right (y i) (K / 4); linarith
  have hor : z = y i ∨ 4 * z = K := by
    rcases min_choice (y i) (K / 4) with h | h
    · left; rw [hz, h]
    · right; rw [hz, h]; ring
  have hdev := hNE i (M.Ω + M.γ * pw.1 (rival i) - z) (z + M.β * pw.2 (rival i))
  rw [dev_prof M y pw i z hz0.le hzy] at hdev
  have Q := quad K (y i) m z h0 h1 hzy hzK hor
  have heq : (K - 2 * m) * m = (K - 2 * z) * z := le_antisymm Q.1 (by linarith)
  have hmz := Q.2 heq
  have hprofeq : M.ksProfit y pw i = (K - 2 * m) * m := le_antisymm h2 (by linarith)
  obtain ⟨e1, e2⟩ := h3 hm hprofeq
  refine ⟨hm, h1, by rw [hmz]; exact hzK, ?_, e1, e2, hprofeq⟩
  rw [hmz]; exact hor

lemma fix_of_pos (M : Model) (hM : M.Standing) (y : Fin 2 → ℝ)
    (pw : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hy : ∀ i, 0 ≤ y i) (hNE : M.IsSubNE y pw)
    (hpos : ∀ i, 0 < M.ksProfit y pw i) :
    (∀ i, 0 ≤ M.ksMatch y pw i) ∧ FixM M y (M.ksMatch y pw) ∧
    pw = (M.qPrice (M.ksMatch y pw), M.qWage (M.ksMatch y pw)) ∧
    ∀ i, M.ksProfit y pw i =
      ff (Lm M) (sm M) (cm M) (M.ksMatch y pw i) (M.ksMatch y pw (rival i)) := by
  have B := fun i => br_step M y pw i (hy i) hNE (hpos i)
  obtain ⟨g1, g2, g3⟩ := hden M hM
  have hp : pw.1 = M.qPrice (M.ksMatch y pw) := by
    have e0 := (B 0).2.2.2.2.1
    have e1 := (B 1).2.2.2.2.1
    rw [r0] at e0; rw [r1] at e1
    funext i
    fin_cases i
    · show pw.1 0 = M.qPrice (M.ksMatch y pw) 0
      unfold Model.qPrice; rw [r0, eq_div_iff g1]
      linear_combination e0 + M.γ * e1
    · show pw.1 1 = M.qPrice (M.ksMatch y pw) 1
      unfold Model.qPrice; rw [r1, eq_div_iff g1]
      linear_combination e1 + M.γ * e0
  have hw : pw.2 = M.qWage (M.ksMatch y pw) := by
    have e0 := (B 0).2.2.2.2.2.1
    have e1 := (B 1).2.2.2.2.2.1
    rw [r0] at e0; rw [r1] at e1
    funext i
    fin_cases i
    · show pw.2 0 = M.qWage (M.ksMatch y pw) 0
      unfold Model.qWage; rw [r0, eq_div_iff g2]
      linear_combination e0 + M.β * e1
    · show pw.2 1 = M.qWage (M.ksMatch y pw) 1
      unfold Model.qWage; rw [r1, eq_div_iff g2]
      linear_combination e1 + M.β * e0
  have hK : ∀ i, Kf M pw i = Lm M - (sm M - 2) * M.ksMatch y pw i -
      cm M * M.ksMatch y pw (rival i) := by
    intro i
    unfold Kf; rw [hp, hw]; exact K_eq M hM _ i
  refine ⟨fun i => (B i).1.le, ?_, Prod.ext hp hw, ?_⟩
  · intro i
    obtain ⟨_, a1, a2, a3, -⟩ := B i
    rw [hK i] at a2 a3
    refine ⟨a1, by linarith, ?_⟩
    rcases a3 with h | h
    · left; exact h
    · right; linarith
  · intro i
    rw [(B i).2.2.2.2.2.2, hK i]; unfold ff; ring

lemma exists_fixM (M : Model) (hM : M.Standing) (y : Fin 2 → ℝ) (hy : ∀ i, 0 ≤ y i) :
    ∃ m : Fin 2 → ℝ, (∀ i, 0 ≤ m i) ∧ FixM M y m := by
  obtain ⟨m1, m2, h1, h2, F1, F2⟩ := exists_fix (par_of M hM) (hy 0) (hy 1)
  refine ⟨![m1, m2], ?_, ?_⟩
  · intro i; fin_cases i
    · exact h1
    · exact h2
  · intro i; fin_cases i
    · show Fx _ _ _ (y 0) (![m1, m2] 0) (![m1, m2] (rival 0))
      rw [r0]; simpa using F1
    · show Fx _ _ _ (y 1) (![m1, m2] 1) (![m1, m2] (rival 1))
      rw [r1]; simpa using F2

open Classical in
noncomputable def mf (M : Model) (y : Fin 2 → ℝ) : Fin 2 → ℝ :=
  if h : ∃ m : Fin 2 → ℝ, (∀ i, 0 ≤ m i) ∧ FixM M y m then Classical.choose h else 0

lemma mf_spec (M : Model) (hM : M.Standing) (y : Fin 2 → ℝ) (hy : ∀ i, 0 ≤ y i) :
    (∀ i, 0 ≤ mf M y i) ∧ FixM M y (mf M y) := by
  have h := exists_fixM M hM y hy
  unfold mf; rw [dif_pos h]; exact Classical.choose_spec h

noncomputable def σ0 (M : Model) (y : Fin 2 → ℝ) : (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  (M.qPrice (mf M y), M.qWage (mf M y))

lemma zero_prof (M : Model) (y : Fin 2 → ℝ) (pw : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (k : Fin 2)
    (h : y k = 0) : M.ksProfit y pw k = 0 := by
  obtain ⟨h0, h1, -, -⟩ := prof_le M y pw k (le_of_eq h.symm)
  have : M.ksMatch y pw k = 0 := le_antisymm (h ▸ h1) h0
  show (pw.1 k - pw.2 k) * M.ksMatch y pw k = 0
  rw [this, mul_zero]

lemma sel0 (M : Model) (hM : M.Standing) (y : Fin 2 → ℝ) (hy : ∀ i, 0 ≤ y i) :
    M.IsSelSubNE y (σ0 M y) ∧ ∀ i, 0 < y i → 0 < M.ksProfit y (σ0 M y) i := by
  obtain ⟨hm, hF⟩ := mf_spec M hM y hy
  obtain ⟨_, _, hNE, hposi⟩ := ne_of_fix M hM y (mf M y) hy hm hF
  refine ⟨⟨hNE, ?_⟩, hposi⟩
  rintro i ⟨pw', _, hp'⟩
  rcases eq_or_lt_of_le (hy i) with h | h
  · exfalso
    have := zero_prof M y pw' i h.symm
    linarith
  · exact hposi i h

end Glue

end KSAux

open PlatformPrecommit.KS KSAux in
theorem solution (M : Model) (hM : M.Standing)
    (q : Fin 2 → ℝ) (pw : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (i : Fin 2)
    (hqAll : ∀ j, 0 ≤ q j) (hq : 0 < q i)
    (hmarket : 0 < M.Ω + M.γ * pw.1 (rival i) - M.β * pw.2 (rival i)) :
    let z : ℝ := min (q i)
      ((M.Ω + M.γ * pw.1 (rival i) - M.β * pw.2 (rival i)) / 4)
    let pStar : ℝ := M.Ω + M.γ * pw.1 (rival i) - z
    let wStar : ℝ := z + M.β * pw.2 (rival i)
    let best := (Function.update pw.1 i pStar, Function.update pw.2 i wStar)
    (∀ a b : ℝ,
      M.ksProfit q (Function.update pw.1 i a, Function.update pw.2 i b) i ≤
        M.ksProfit q best i ∧
      (M.ksProfit q (Function.update pw.1 i a, Function.update pw.2 i b) i =
        M.ksProfit q best i → a = pStar ∧ b = wStar)) ∧
    M.ksProfit q best i =
      (M.Ω + M.γ * pw.1 (rival i) - M.β * pw.2 (rival i) - 2 * z) * z := by
  intro z pStar wStar best
  set K := M.Ω + M.γ * pw.1 (rival i) - M.β * pw.2 (rival i) with hK
  have hz0 : 0 < z := lt_min hq (by linarith)
  have hzy : z ≤ q i := min_le_left _ _
  have hzK : 4 * z ≤ K := by have := min_le_right (q i) (K / 4); linarith
  have hor : z = q i ∨ 4 * z = K := by
    rcases min_choice (q i) (K / 4) with h | h
    · left; exact h
    · right; show 4 * min (q i) (K / 4) = K; rw [h]; ring
  have hbest : M.ksProfit q best i = (K - 2 * z) * z := dev_prof M q pw i z hz0.le hzy
  refine ⟨?_, hbest⟩
  intro a b
  obtain ⟨h0, h1, h2, h3⟩ := prof_le M q (Function.update pw.1 i a, Function.update pw.2 i b) i (hqAll i)
  have hKf : Kf M (Function.update pw.1 i a, Function.update pw.2 i b) i = K := by
    unfold Kf; simp only [Function.update_of_ne (rival_ne i)]
    try exact hK.symm
  rw [hKf] at h2 h3
  have Q := quad K (q i) _ z h0 h1 hzy hzK hor
  refine ⟨by rw [hbest]; linarith [Q.1], ?_⟩
  intro he
  rw [hbest] at he
  have heq : (K - 2 * M.ksMatch q (Function.update pw.1 i a, Function.update pw.2 i b) i) *
      M.ksMatch q (Function.update pw.1 i a, Function.update pw.2 i b) i = (K - 2 * z) * z :=
    le_antisymm Q.1 (by linarith)
  have hmz := Q.2 heq
  obtain ⟨e1, e2⟩ := h3 (by rw [hmz]; exact hz0) (by rw [he, heq])
  simp only [Function.update_self, Function.update_of_ne (rival_ne i)] at e1 e2
  rw [hmz] at e1 e2
  exact ⟨e1, e2⟩
