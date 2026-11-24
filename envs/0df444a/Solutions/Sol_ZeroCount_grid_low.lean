-- Prove2me | solution 1 for ZeroCount.grid_low
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T04:05:57.746555+00:00
-- url     : https://prove2.me/submissions/c380839e-22d6-47c9-bfc7-279e897f4a78

import Mathlib
import Definitions.Def_ArdaRH65K_RS5_Band
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group000
import Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group001
import Theorems.Thm_ZeroCount_tail_zeros

open Complex

namespace ZC

noncomputable def Rf (t : ℝ) : ℝ := t / (2 * Real.pi) * (Real.log (t / (2 * Real.pi)) - 1) + 5 / 2

def P (a : ℝ) (A : ℕ) : Prop :=
  ∃ s : Finset ℝ, s.card = A ∧ ∀ x ∈ s, a < x ∧ x ≤ 65000 ∧ riemannZeta (1 / 2 + (x : ℂ) * I) = 0

def Good (t : ℝ) : Prop :=
  ∃ s : Finset ℝ, (85288 : ℝ) - s.card ≤ Rf t ∧
    ∀ x ∈ s, t < x ∧ x ≤ 65000 ∧ riemannZeta (1 / 2 + (x : ℂ) * I) = 0

theorem P_mono {a t : ℝ} {A : ℕ} (h : P a A) (ht : t ≤ a) : P t A := by
  obtain ⟨s, hs, hx⟩ := h
  exact ⟨s, hs, fun x hxs => ⟨lt_of_le_of_lt ht (hx x hxs).1, (hx x hxs).2⟩⟩

theorem P_glue {T0 T1 a : ℝ} {K B : ℕ} (hb : RS5.BandZeros T0 T1 K) (h01 : T0 ≤ T1) (hT : T1 ≤ a)
    (hT6 : T1 ≤ 65000) (hP : P a B) : P T0 (K + B) := by
  classical
  obtain ⟨xs, hlen, hch, hbd, hz⟩ := hb
  obtain ⟨s, hs, hx⟩ := hP
  have hnd : xs.Nodup := (List.isChain_iff_pairwise.mp hch).imp (fun h => ne_of_lt h)
  have hdisj : Disjoint xs.toFinset s := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 := (hbd x (List.mem_toFinset.mp hx1)).2
    have h2 := (hx x hx2).1
    linarith
  refine ⟨xs.toFinset ∪ s, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, List.toFinset_card_of_nodup hnd, hlen, hs]
  · intro x hxm
    rcases Finset.mem_union.mp hxm with h | h
    · have hm := List.mem_toFinset.mp h
      exact ⟨(hbd x hm).1, by linarith [(hbd x hm).2], (hz x hm).2⟩
    · have h2 := (hx x h).1
      exact ⟨by linarith, (hx x h).2⟩

/-! ## The rational lower bound for `Rf` -/

def ser (y : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => ser y n + y ^ (n + 1) / (n + 1)

theorem ser_cast (y : ℚ) (n : ℕ) :
    ((ser y n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (y : ℝ) ^ (i + 1) / (i + 1) := by
  induction n with
  | zero => simp [ser]
  | succ n ih => rw [ser, Finset.sum_range_succ, ← ih]; push_cast; ring

def okR (tn tq c : ℕ) : Bool :=
  let x : ℚ := (tn : ℚ) / 2 ^ tq
  let u : ℚ := x / (2 * (31416 / 10000))
  let m := Nat.log2 u.floor.toNat
  let y : ℚ := 1 - 2 ^ m / u
  let L : ℚ := m * (6931471803 / 10 ^ 10) + ser y 22 - y ^ 23 / (1 - y)
  decide (1 ≤ u) && decide (0 ≤ y) && decide (y < 1) &&
    decide ((85288 : ℚ) - c ≤ u * (L - 1) + 5 / 2)

theorem f_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    a * (Real.log a - 1) ≤ b * (Real.log b - 1) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha
  have h1 : 1 - a / b ≤ Real.log (b / a) := by
    have := Real.one_sub_inv_le_log_of_pos (show 0 < b / a by positivity)
    rwa [inv_div] at this
  rw [Real.log_div hb0.ne' ha0.ne'] at h1
  have h2 : b * (1 - a / b) = b - a := by field_simp
  have h3 : b - a ≤ b * (Real.log b - Real.log a) := by
    rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hb0.le
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) hla]

theorem log_lower (u y : ℝ) (m n : ℕ) (hu : 0 < u) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hy : y = 1 - 2 ^ m / u) :
    m * (6931471803 / 10 ^ 10) + (∑ i ∈ Finset.range n, y ^ (i + 1) / (i + 1)) -
      y ^ (n + 1) / (1 - y) ≤ Real.log u := by
  have hab := Real.abs_log_sub_add_sum_range_le (show |y| < 1 by rw [abs_of_nonneg hy0]; exact hy1) n
  rw [abs_of_nonneg hy0] at hab
  have h1 := (abs_le.mp hab).2
  have h1y : 1 - y = 2 ^ m / u := by rw [hy]; ring
  have hl : Real.log (1 - y) = m * Real.log 2 - Real.log u := by
    rw [h1y, Real.log_div (by positivity) hu.ne', Real.log_pow]
  have hl2 := Real.log_two_gt_d9
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [hl] at h1
  nlinarith [mul_le_mul_of_nonneg_left hl2.le hm]

theorem okR_sound {tn tq c : ℕ} (h : okR tn tq c = true) {t : ℝ}
    (ht : (tn : ℝ) / 2 ^ tq ≤ t) : (85288 : ℝ) - c ≤ Rf t := by
  simp only [okR, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  set x : ℚ := (tn : ℚ) / 2 ^ tq with hx
  set u : ℚ := x / (2 * (31416 / 10000)) with hu
  set m := Nat.log2 u.floor.toNat
  set y : ℚ := 1 - 2 ^ m / u with hy
  have h1' : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast h1
  have h2' : (0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast h2
  have h3' : (y : ℝ) < 1 := by exact_mod_cast h3
  have hu0 : (0 : ℝ) < (u : ℝ) := by linarith
  have hyR : (y : ℝ) = 1 - 2 ^ m / (u : ℝ) := by rw [hy]; push_cast; ring
  have hL := log_lower (u : ℝ) (y : ℝ) m 22 hu0 h2' h3' hyR
  have h4' := (Rat.cast_le (K := ℝ)).mpr h4
  push_cast [ser_cast] at h4'
  have hxR : ((x : ℚ) : ℝ) = (tn : ℝ) / 2 ^ tq := by rw [hx]; push_cast; ring
  have huR : (u : ℝ) = (x : ℝ) / (2 * (31416 / 10000)) := by rw [hu]; push_cast; ring
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have hut : (u : ℝ) ≤ t / (2 * Real.pi) := by
    rw [huR, hxR]
    have hx0 : 0 ≤ (tn : ℝ) / 2 ^ tq := by positivity
    calc (tn : ℝ) / 2 ^ tq / (2 * (31416 / 10000)) ≤ (tn : ℝ) / 2 ^ tq / (2 * Real.pi) :=
          div_le_div_of_nonneg_left hx0 (by positivity) (by linarith)
      _ ≤ t / (2 * Real.pi) := div_le_div_of_nonneg_right ht (by positivity)
  have hf := f_mono h1' hut
  unfold Rf
  have := mul_le_mul_of_nonneg_left (sub_le_sub_right hL 1) hu0.le
  linarith

/-! ## The abstract list engine -/

def chk {α : Type} (tn tq : α → ℕ) (cnt : List α → ℕ) (B : ℕ) : α → List α → Bool
  | s, [] => okR (tn s) (tq s) B
  | s, b :: rest => okR (tn s) (tq s) (cnt (b :: rest) + B) &&
      decide (tn s * 2 ^ tq b ≤ tn b * 2 ^ tq s) && chk tn tq cnt B b rest

theorem hle_of {n1 q1 n2 q2 : ℕ} (h : n1 * 2 ^ q2 ≤ n2 * 2 ^ q1) :
    (n1 : ℝ) / 2 ^ q1 ≤ (n2 : ℝ) / 2 ^ q2 := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast h

theorem chk_last {α : Type} (tn tq : α → ℕ) (cnt : List α → ℕ) (B : ℕ) :
    ∀ (l : List α) (s : α), chk tn tq cnt B s l = true →
      (tn s : ℝ) / 2 ^ tq s ≤ (tn (RS5.lastOf s l) : ℝ) / 2 ^ tq (RS5.lastOf s l) := by
  intro l
  induction l with
  | nil => intro s _; exact le_refl _
  | cons b rest ih =>
    intro s h
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact le_trans (hle_of h.1.2) (ih b h.2)

theorem eng {α : Type} (tn tq : α → ℕ) (cnt : List α → ℕ) (Q : List α → Prop)
    (hQt : ∀ a l, Q (a :: l) → Q l)
    (hQb : ∀ b rest, Q (b :: rest) → RS5.BandZeros ((tn b : ℝ) / 2 ^ tq b)
      ((tn (RS5.lastOf b rest) : ℝ) / 2 ^ tq (RS5.lastOf b rest)) (cnt (b :: rest)))
    (B : ℕ) (T' : ℝ) (hP : P T' B) (hT6 : T' ≤ 65000) :
    ∀ (l : List α) (s0 : α), Q (s0 :: l) →
      (tn (RS5.lastOf s0 l) : ℝ) / 2 ^ tq (RS5.lastOf s0 l) ≤ T' →
      chk tn tq cnt B s0 l = true →
      ∀ t, (tn s0 : ℝ) / 2 ^ tq s0 ≤ t → t < T' → Good t := by
  intro l
  induction l with
  | nil =>
    intro s0 _ _ hc t ht0 ht1
    obtain ⟨s, hs, hx⟩ := hP
    refine ⟨s, ?_, fun x hxs => ⟨lt_trans ht1 (hx x hxs).1, (hx x hxs).2⟩⟩
    rw [hs]; exact okR_sound hc ht0
  | cons b rest ih =>
    intro s0 hQ hlast hc t ht0 ht1
    have hc' := hc
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at hc'
    obtain ⟨⟨hok, _⟩, hrest⟩ := hc'
    have hlast' : (tn (RS5.lastOf b rest) : ℝ) / 2 ^ tq (RS5.lastOf b rest) ≤ T' := hlast
    by_cases htb : t < (tn b : ℝ) / 2 ^ tq b
    · have hPb := P_glue (hQb b rest (hQt _ _ hQ)) (chk_last tn tq cnt B rest b hrest) hlast'
        (le_trans hlast' hT6) hP
      obtain ⟨s, hs, hx⟩ := hPb
      refine ⟨s, ?_, fun x hxs => ⟨lt_trans htb (hx x hxs).1, (hx x hxs).2⟩⟩
      rw [hs]; push_cast; exact_mod_cast okR_sound hok ht0
    · push Not at htb
      exact ih b (hQt _ _ hQ) hlast' hrest t htb ht1

theorem engP {α : Type} (tn tq : α → ℕ) (cnt : List α → ℕ) (Q : List α → Prop)
    (hQb : ∀ b rest, Q (b :: rest) → RS5.BandZeros ((tn b : ℝ) / 2 ^ tq b)
      ((tn (RS5.lastOf b rest) : ℝ) / 2 ^ tq (RS5.lastOf b rest)) (cnt (b :: rest)))
    (B : ℕ) (T' : ℝ) (hP : P T' B) (hT6 : T' ≤ 65000) (l : List α) (s0 : α) (hQ : Q (s0 :: l))
    (hlast : (tn (RS5.lastOf s0 l) : ℝ) / 2 ^ tq (RS5.lastOf s0 l) ≤ T')
    (hc : chk tn tq cnt B s0 l = true) :
    P ((tn s0 : ℝ) / 2 ^ tq s0) (cnt (s0 :: l) + B) :=
  P_glue (hQb s0 l hQ) (chk_last tn tq cnt B l s0 hc) hlast (le_trans hlast hT6) hP

end ZC

namespace ZC

noncomputable def dummy : RS5.Sample :=
  ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩

theorem bandOK_tail (a : RS5.Sample) (l : List RS5.Sample) (h : RS5.bandOK (a :: l) = true) :
    RS5.bandOK l = true := by
  cases l with
  | nil => rfl
  | cons b rest =>
    have e : RS5.bandOK (a :: b :: rest) =
        (RS5.sampleOK a && RS5.ltH a b && RS5.bandAux rest b) := rfl
    rw [e] at h
    simp only [Bool.and_eq_true] at h
    exact h.2

theorem rsStep (L : List RS5.Sample) (n0 q0 n1 q1 K B : ℕ)
    (hP : P ((n1 : ℝ) / 2 ^ q1) B) (h6 : (n1 : ℝ) / 2 ^ q1 ≤ 65000)
    (hok : RS5.bandOK L = true)
    (hf : decide ((L.getD 0 dummy).tn = n0 ∧ (L.getD 0 dummy).tq = q0 ∧
      (RS5.lastOf (L.getD 0 dummy) (L.drop 1)).tn = n1 ∧
      (RS5.lastOf (L.getD 0 dummy) (L.drop 1)).tq = q1 ∧
      RS5.chgBy RS5.Sample.pos L = K ∧ L ≠ []) = true)
    (hc : chk RS5.Sample.tn RS5.Sample.tq (RS5.chgBy RS5.Sample.pos) B
      (L.getD 0 dummy) (L.drop 1) = true) :
    (∀ t, (n0 : ℝ) / 2 ^ q0 ≤ t → t < (n1 : ℝ) / 2 ^ q1 → Good t) ∧
      P ((n0 : ℝ) / 2 ^ q0) (K + B) := by
  simp only [decide_eq_true_eq] at hf
  obtain ⟨e0, e1, e2, e3, e4, hne⟩ := hf
  obtain ⟨a, l, rfl⟩ : ∃ a l, L = a :: l := List.exists_cons_of_ne_nil hne
  simp only [List.getD_cons_zero, List.drop_succ_cons, List.drop_zero] at e0 e1 e2 e3 hc
  subst e0 e1 e2 e3 e4
  have hQb : ∀ b rest, RS5.bandOK (b :: rest) = true → RS5.BandZeros ((b.tn : ℝ) / 2 ^ b.tq)
      (((RS5.lastOf b rest).tn : ℝ) / 2 ^ (RS5.lastOf b rest).tq)
      (RS5.chgBy RS5.Sample.pos (b :: rest)) := fun b rest h => RS5.bandZeros_of_ok b rest h
  exact ⟨eng RS5.Sample.tn RS5.Sample.tq (RS5.chgBy RS5.Sample.pos) (fun l => RS5.bandOK l = true)
      bandOK_tail hQb B _ hP h6 l a hok le_rfl hc,
    engP RS5.Sample.tn RS5.Sample.tq (RS5.chgBy RS5.Sample.pos) (fun l => RS5.bandOK l = true)
      hQb B _ hP h6 l a hok le_rfl hc⟩

end ZC
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ZC

theorem P_top : P 65000 0 := ⟨∅, rfl, by simp⟩

theorem tailP : P (((168028858 : ℕ) : ℝ) / 2 ^ 16) 83242 := by
  have h := ZeroCount.tail_zeros
  have e : ((168028858 : ℝ) / 65536) = ((168028858 : ℕ) : ℝ) / 2 ^ 16 := by norm_num
  rw [e] at h
  exact P_glue h (by norm_num) le_rfl le_rfl P_top

end ZC
open ZC
namespace ZC.GridLow
theorem ok_RH65K_Low_0010 : RS5.bandOK RH65K_Low_0010.samples = true := ((((TaoFivePrimes.arda_rh65k_low_arithmetic_group001).2).2).1).1
theorem s_RH65K_Low_0010 : (∀ t, (((159313983 : ℕ) : ℝ) / 2 ^ 16) ≤ t → t < (((168028858 : ℕ) : ℝ) / 2 ^ 16) → Good t) ∧ P (((159313983 : ℕ) : ℝ) / 2 ^ 16) 83369 :=
  rsStep RH65K_Low_0010.samples 159313983 16 168028858 16 127 83242 tailP (by norm_num) ok_RH65K_Low_0010 (by decide +kernel) (by decide +kernel)
theorem ok_RH65K_Low_0009 : RS5.bandOK RH65K_Low_0009.samples = true := (((TaoFivePrimes.arda_rh65k_low_arithmetic_group001).2).1).1
theorem s_RH65K_Low_0009 : (∀ t, (((150507146 : ℕ) : ℝ) / 2 ^ 16) ≤ t → t < (((159313983 : ℕ) : ℝ) / 2 ^ 16) → Good t) ∧ P (((150507146 : ℕ) : ℝ) / 2 ^ 16) 83496 :=
  rsStep RH65K_Low_0009.samples 150507146 16 159313983 16 127 83369 s_RH65K_Low_0010.2 (by norm_num) ok_RH65K_Low_0009 (by decide +kernel) (by decide +kernel)
theorem ok_RH65K_Low_0008 : RS5.bandOK RH65K_Low_0008.samples = true := ((TaoFivePrimes.arda_rh65k_low_arithmetic_group001).1).1
theorem s_RH65K_Low_0008 : (∀ t, (((141582511 : ℕ) : ℝ) / 2 ^ 16) ≤ t → t < (((150507146 : ℕ) : ℝ) / 2 ^ 16) → Good t) ∧ P (((141582511 : ℕ) : ℝ) / 2 ^ 16) 83623 :=
  rsStep RH65K_Low_0008.samples 141582511 16 150507146 16 127 83496 s_RH65K_Low_0009.2 (by norm_num) ok_RH65K_Low_0008 (by decide +kernel) (by decide +kernel)
theorem ok_RH65K_Low_0007 : RS5.bandOK RH65K_Low_0007.samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group000).2).2).2).2).2).2).2).1
theorem s_RH65K_Low_0007 : (∀ t, (((132583211 : ℕ) : ℝ) / 2 ^ 16) ≤ t → t < (((141582511 : ℕ) : ℝ) / 2 ^ 16) → Good t) ∧ P (((132583211 : ℕ) : ℝ) / 2 ^ 16) 83750 :=
  rsStep RH65K_Low_0007.samples 132583211 16 141582511 16 127 83623 s_RH65K_Low_0008.2 (by norm_num) ok_RH65K_Low_0007 (by decide +kernel) (by decide +kernel)
theorem ok_RH65K_Low_0006 : RS5.bandOK RH65K_Low_0006.samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group000).2).2).2).2).2).2).1).1
theorem s_RH65K_Low_0006 : (∀ t, (((123450638 : ℕ) : ℝ) / 2 ^ 16) ≤ t → t < (((132583211 : ℕ) : ℝ) / 2 ^ 16) → Good t) ∧ P (((123450638 : ℕ) : ℝ) / 2 ^ 16) 83877 :=
  rsStep RH65K_Low_0006.samples 123450638 16 132583211 16 127 83750 s_RH65K_Low_0007.2 (by norm_num) ok_RH65K_Low_0006 (by decide +kernel) (by decide +kernel)
theorem ok_RH65K_Low_0005 : RS5.bandOK RH65K_Low_0005.samples = true := (((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group000).2).2).2).2).2).1).1
theorem s_RH65K_Low_0005 : (∀ t, (((114225778 : ℕ) : ℝ) / 2 ^ 16) ≤ t → t < (((123450638 : ℕ) : ℝ) / 2 ^ 16) → Good t) ∧ P (((114225778 : ℕ) : ℝ) / 2 ^ 16) 84004 :=
  rsStep RH65K_Low_0005.samples 114225778 16 123450638 16 127 83877 s_RH65K_Low_0006.2 (by norm_num) ok_RH65K_Low_0005 (by decide +kernel) (by decide +kernel)
theorem ok_RH65K_Low_0004 : RS5.bandOK RH65K_Low_0004.samples = true := ((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group000).2).2).2).2).1).1
theorem s_RH65K_Low_0004 : (∀ t, (((104846701 : ℕ) : ℝ) / 2 ^ 16) ≤ t → t < (((114225778 : ℕ) : ℝ) / 2 ^ 16) → Good t) ∧ P (((104846701 : ℕ) : ℝ) / 2 ^ 16) 84131 :=
  rsStep RH65K_Low_0004.samples 104846701 16 114225778 16 127 84004 s_RH65K_Low_0005.2 (by norm_num) ok_RH65K_Low_0004 (by decide +kernel) (by decide +kernel)
theorem ok_RH65K_Low_0003 : RS5.bandOK RH65K_Low_0003.samples = true := (((((TaoFivePrimes.arda_rh65k_low_arithmetic_group000).2).2).2).1).1
theorem s_RH65K_Low_0003 : (∀ t, (((95339744 : ℕ) : ℝ) / 2 ^ 16) ≤ t → t < (((104846701 : ℕ) : ℝ) / 2 ^ 16) → Good t) ∧ P (((95339744 : ℕ) : ℝ) / 2 ^ 16) 84258 :=
  rsStep RH65K_Low_0003.samples 95339744 16 104846701 16 127 84131 s_RH65K_Low_0004.2 (by norm_num) ok_RH65K_Low_0003 (by decide +kernel) (by decide +kernel)
theorem ok_RH65K_Low_0002 : RS5.bandOK RH65K_Low_0002.samples = true := ((((TaoFivePrimes.arda_rh65k_low_arithmetic_group000).2).2).1).1
theorem s_RH65K_Low_0002 : (∀ t, (((85648200 : ℕ) : ℝ) / 2 ^ 16) ≤ t → t < (((95339744 : ℕ) : ℝ) / 2 ^ 16) → Good t) ∧ P (((85648200 : ℕ) : ℝ) / 2 ^ 16) 84385 :=
  rsStep RH65K_Low_0002.samples 85648200 16 95339744 16 127 84258 s_RH65K_Low_0003.2 (by norm_num) ok_RH65K_Low_0002 (by decide +kernel) (by decide +kernel)
theorem ok_RH65K_Low_0001 : RS5.bandOK RH65K_Low_0001.samples = true := (((TaoFivePrimes.arda_rh65k_low_arithmetic_group000).2).1).1
theorem s_RH65K_Low_0001 : (∀ t, (((75737303 : ℕ) : ℝ) / 2 ^ 16) ≤ t → t < (((85648200 : ℕ) : ℝ) / 2 ^ 16) → Good t) ∧ P (((75737303 : ℕ) : ℝ) / 2 ^ 16) 84512 :=
  rsStep RH65K_Low_0001.samples 75737303 16 85648200 16 127 84385 s_RH65K_Low_0002.2 (by norm_num) ok_RH65K_Low_0001 (by decide +kernel) (by decide +kernel)
theorem ok_RH65K_Low_0000 : RS5.bandOK RH65K_Low_0000.samples = true := ((TaoFivePrimes.arda_rh65k_low_arithmetic_group000).1).1
theorem s_RH65K_Low_0000 : (∀ t, (((65573390 : ℕ) : ℝ) / 2 ^ 16) ≤ t → t < (((75737303 : ℕ) : ℝ) / 2 ^ 16) → Good t) ∧ P (((65573390 : ℕ) : ℝ) / 2 ^ 16) 84639 :=
  rsStep RH65K_Low_0000.samples 65573390 16 75737303 16 127 84512 s_RH65K_Low_0001.2 (by norm_num) ok_RH65K_Low_0000 (by decide +kernel) (by decide +kernel)
theorem region : (∀ t, (((65573390 : ℕ) : ℝ) / 2 ^ 16) ≤ t → t < (((168028858 : ℕ) : ℝ) / 2 ^ 16) → Good t) ∧ P (((65573390 : ℕ) : ℝ) / 2 ^ 16) 84639 := by
  refine ⟨fun t h0 h1 => ?_, s_RH65K_Low_0000.2⟩
  by_cases c0 : t < (((75737303 : ℕ) : ℝ) / 2 ^ 16)
  · exact s_RH65K_Low_0000.1 t (by linarith) c0
  push Not at c0
  by_cases c1 : t < (((85648200 : ℕ) : ℝ) / 2 ^ 16)
  · exact s_RH65K_Low_0001.1 t (by linarith) c1
  push Not at c1
  by_cases c2 : t < (((95339744 : ℕ) : ℝ) / 2 ^ 16)
  · exact s_RH65K_Low_0002.1 t (by linarith) c2
  push Not at c2
  by_cases c3 : t < (((104846701 : ℕ) : ℝ) / 2 ^ 16)
  · exact s_RH65K_Low_0003.1 t (by linarith) c3
  push Not at c3
  by_cases c4 : t < (((114225778 : ℕ) : ℝ) / 2 ^ 16)
  · exact s_RH65K_Low_0004.1 t (by linarith) c4
  push Not at c4
  by_cases c5 : t < (((123450638 : ℕ) : ℝ) / 2 ^ 16)
  · exact s_RH65K_Low_0005.1 t (by linarith) c5
  push Not at c5
  by_cases c6 : t < (((132583211 : ℕ) : ℝ) / 2 ^ 16)
  · exact s_RH65K_Low_0006.1 t (by linarith) c6
  push Not at c6
  by_cases c7 : t < (((141582511 : ℕ) : ℝ) / 2 ^ 16)
  · exact s_RH65K_Low_0007.1 t (by linarith) c7
  push Not at c7
  by_cases c8 : t < (((150507146 : ℕ) : ℝ) / 2 ^ 16)
  · exact s_RH65K_Low_0008.1 t (by linarith) c8
  push Not at c8
  by_cases c9 : t < (((159313983 : ℕ) : ℝ) / 2 ^ 16)
  · exact s_RH65K_Low_0009.1 t (by linarith) c9
  push Not at c9
  exact s_RH65K_Low_0010.1 t (by linarith) h1
end ZC.GridLow
theorem solution :
    (∀ t : ℝ, (65573390 : ℝ) / 65536 ≤ t → t < (168028858 : ℝ) / 65536 →
      ∃ s : Finset ℝ, (85288 : ℝ) - s.card ≤
          t / (2 * Real.pi) * (Real.log (t / (2 * Real.pi)) - 1) + 5 / 2 ∧
        ∀ x ∈ s, t < x ∧ x ≤ 65000 ∧ riemannZeta (1 / 2 + (x : ℂ) * Complex.I) = 0) ∧
    (∃ s : Finset ℝ, s.card = 84639 ∧
      ∀ x ∈ s, (65573390 : ℝ) / 65536 < x ∧ x ≤ 65000 ∧
        riemannZeta (1 / 2 + (x : ℂ) * Complex.I) = 0) := by
  obtain ⟨h1, h2⟩ := ZC.GridLow.region
  have e0 : (((65573390 : ℕ) : ℝ) / 2 ^ 16) = (65573390 : ℝ) / 65536 := by norm_num
  have e1 : (((168028858 : ℕ) : ℝ) / 2 ^ 16) = (168028858 : ℝ) / 65536 := by norm_num
  rw [e0, e1] at h1
  rw [e0] at h2
  exact ⟨h1, h2⟩
