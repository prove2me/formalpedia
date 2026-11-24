-- Prove2me | solution 1 for ZeroCount.grid_B
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T04:23:04.825731+00:00
-- url     : https://prove2.me/submissions/e646ba4e-19d2-4978-a8a2-1b6312e75c30

import Mathlib
import Definitions.Def_ArdaRH65K_RS5_Band
import Theorems.Thm_Arb4_bandC_sound
import Theorems.Thm_Arb4_ptCheckC_sound
import Definitions.Def_ArdaRH65K_Turing121_Arb4_H1000Lines_0
import Definitions.Def_ArdaRH65K_Turing121_Arb4_H1000Lines_1
import Definitions.Def_ArdaRH65K_Turing121_Arb4_H1000Lines_2
import Theorems.Thm_Arb4_allC_append
import Theorems.Thm_Arb4_H1000_B03_0_ok
import Theorems.Thm_Arb4_H1000_B03_1_ok
import Theorems.Thm_Arb4_H1000_B03_2_ok
import Theorems.Thm_Arb4_H1000_B04_0_ok
import Theorems.Thm_Arb4_H1000_B04_1_ok
import Theorems.Thm_Arb4_H1000_B04_2_ok
import Theorems.Thm_Arb4_H1000_B04_3_ok
import Theorems.Thm_Arb4_H1000_B05_0_ok
import Theorems.Thm_Arb4_H1000_B05_1_ok
import Theorems.Thm_Arb4_H1000_B05_2_ok
import Theorems.Thm_Arb4_H1000_B05_3_ok
import Theorems.Thm_Arb4_H1000_B06_0_ok
import Theorems.Thm_Arb4_H1000_B06_1_ok
import Theorems.Thm_Arb4_H1000_B06_2_ok
import Theorems.Thm_Arb4_H1000_B06_3_ok
import Theorems.Thm_Arb4_H1000_B07_0_ok
import Theorems.Thm_Arb4_H1000_B07_1_ok
import Theorems.Thm_Arb4_H1000_B07_2_ok
import Theorems.Thm_Arb4_H1000_B07_3_ok
import Theorems.Thm_Arb4_H1000_B08_0_ok
import Theorems.Thm_Arb4_H1000_B08_1_ok
import Theorems.Thm_Arb4_H1000_B08_2_ok
import Theorems.Thm_Arb4_H1000_B08_3_ok
import Theorems.Thm_Arb4_H1000_B09_0_ok
import Theorems.Thm_Arb4_H1000_B09_1_ok
import Theorems.Thm_Arb4_H1000_B09_2_ok
import Theorems.Thm_Arb4_H1000_B09_3_ok
import Theorems.Thm_Arb4_H1000_B10_0_ok
import Theorems.Thm_Arb4_H1000_B10_1_ok
import Theorems.Thm_Arb4_H1000_B10_2_ok
import Theorems.Thm_Arb4_H1000_B10_3_ok
import Theorems.Thm_Arb4_H1000_B11_0_ok
import Theorems.Thm_Arb4_H1000_B11_1_ok
import Theorems.Thm_Arb4_H1000_B11_2_ok
import Theorems.Thm_Arb4_H1000_B11_3_ok
import Theorems.Thm_Arb4_H1000_B12_0_ok
import Theorems.Thm_Arb4_H1000_B12_1_ok
import Theorems.Thm_Arb4_H1000_B12_2_ok
import Theorems.Thm_Arb4_H1000_B12_3_ok
import Theorems.Thm_ZeroCount_grid_bridge

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

open Complex Arb4 H1000Line

namespace ZC

noncomputable def dummyP : PtD := ⟨0, 0, 0, 0, 0, 0, 0, 0, false⟩

def QP (l : List PtD) : Prop :=
  l.all (fun d => ptCheckC d.pt) = true ∧ H1000Line.chainOk (l.map PtD.pt) = true

theorem QP_tail (a : PtD) (l : List PtD) (h : QP (a :: l)) : QP l := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [List.all_cons, Bool.and_eq_true] at h1; exact h1.2
  · cases l with
    | nil => rfl
    | cons b rest =>
      simp only [List.map_cons, H1000Line.chainOk, Bool.and_eq_true] at h2
      simpa only [List.map_cons] using h2.2

theorem lastLe_lastOf : ∀ (rest : List PtD) (b : PtD),
    H1000Line.lastLe (RS5.lastOf b rest).tn (2 ^ (RS5.lastOf b rest).tq)
      ((b :: rest).map PtD.pt) = true := by
  intro rest
  induction rest with
  | nil =>
    intro b
    show decide (b.pt.tn * 2 ^ b.tq ≤ b.tn * 2 ^ b.pt.tq) = true
    exact decide_eq_true (le_refl _)
  | cons c rest ih =>
    intro b
    exact ih c

theorem lastOf_mem : ∀ (rest : List PtD) (b : PtD), RS5.lastOf b rest ∈ b :: rest := by
  intro rest
  induction rest with
  | nil => intro b; simp [RS5.lastOf]
  | cons c rest ih => intro b; exact List.mem_cons_of_mem _ (ih c)

theorem checked_nonzero (d : PtD) (h : ptCheckC d.pt = true) :
    completedRiemannZeta (1 / 2 + (tOf d.pt : ℂ) * I) ≠ 0 := by
  have hs := ptCheckC_sound d h
  have hg : XiLineZeros.gLine (tOf d.pt) ≠ 0 := by
    cases hp : d.pt.pos
    · have hneg := hs.2 hp
      linarith
    · have hpos := hs.1 hp
      linarith
  intro hz
  apply hg
  change (completedRiemannZeta (1 / 2 + (tOf d.pt : ℂ) * I)).re = 0
  rw [hz]
  rfl

theorem tOf_pt (d : PtD) : tOf d.pt = (d.tn : ℝ) / 2 ^ d.tq := rfl

theorem line_to_band {lo hi : ℝ} {K : ℕ}
    (line : ∃ xs : List ℝ, xs.length = K ∧ xs.IsChain (· < ·) ∧
      (∀ t ∈ xs, lo ≤ t ∧ t ≤ hi) ∧
      (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * I) = 0))
    (hlo : completedRiemannZeta (1 / 2 + (lo : ℂ) * I) ≠ 0)
    (hhi : completedRiemannZeta (1 / 2 + (hi : ℂ) * I) ≠ 0) :
    RS5.BandZeros lo hi K := by
  obtain ⟨xs, hlen, hchain, hbd, hz⟩ := line
  refine ⟨xs, hlen, hchain, ?_, ?_⟩
  · intro t ht
    have h := hbd t ht
    have hzero := hz t ht
    have hne0 : lo ≠ t := by
      intro heq
      subst t
      exact hlo hzero
    have hne1 : t ≠ hi := by
      intro heq
      subst t
      exact hhi hzero
    exact ⟨lt_of_le_of_ne h.1 hne0, lt_of_le_of_ne h.2 hne1⟩
  · intro t ht
    have h := hz t ht
    have hne : (1 / 2 + (t : ℂ) * I) ≠ 0 := by
      intro heq
      have hre := congrArg Complex.re heq
      norm_num at hre
    have hzeta : riemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
      rw [riemannZeta_def_of_ne_zero hne, h, zero_div]
    exact ⟨h, hzeta⟩

def cntP (l : List PtD) : ℕ := l.length - 1

theorem QP_band (b : PtD) (rest : List PtD) (h : QP (b :: rest)) :
    RS5.BandZeros ((b.tn : ℝ) / 2 ^ b.tq)
      (((RS5.lastOf b rest).tn : ℝ) / 2 ^ (RS5.lastOf b rest).tq) (cntP (b :: rest)) := by
  obtain ⟨h1, h2⟩ := h
  have hb : bandC b.tn (2 ^ b.tq) (RS5.lastOf b rest).tn (2 ^ (RS5.lastOf b rest).tq)
      rest.length (b :: rest) = true := by
    unfold bandC
    rw [h1, Bool.true_and]
    unfold H1000Line.bandOk
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨⟨by simp, h2⟩, by positivity⟩, by positivity⟩, ?_⟩, lastLe_lastOf rest b⟩
    show decide (b.tn * 2 ^ b.pt.tq ≤ b.pt.tn * 2 ^ b.tq) = true
    exact decide_eq_true (le_refl _)
  have hl := bandC_sound (tOf b.pt) (tOf (RS5.lastOf b rest).pt) _ _ _ _ _
    (by rw [tOf_pt]; push_cast; ring) (by rw [tOf_pt]; push_cast; ring) _ hb
  have hall := List.all_eq_true.mp h1
  have hbz := line_to_band hl (checked_nonzero b (hall b (List.mem_cons_self ..)))
    (checked_nonzero _ (hall _ (lastOf_mem rest b)))
  rw [tOf_pt, tOf_pt] at hbz
  have hc : cntP (b :: rest) = rest.length := by simp [cntP]
  rw [hc]
  exact hbz

theorem ptStep (L : List PtD) (n0 q0 n1 q1 K B : ℕ)
    (hP : P ((n1 : ℝ) / 2 ^ q1) B) (h6 : (n1 : ℝ) / 2 ^ q1 ≤ 65000)
    (hall : L.all (fun d => ptCheckC d.pt) = true)
    (hf : decide ((L.getD 0 dummyP).tn = n0 ∧ (L.getD 0 dummyP).tq = q0 ∧
      (RS5.lastOf (L.getD 0 dummyP) (L.drop 1)).tn * 2 ^ q1 ≤ n1 * 2 ^ (RS5.lastOf (L.getD 0 dummyP) (L.drop 1)).tq ∧
      cntP L = K ∧ L ≠ [] ∧ H1000Line.chainOk (L.map PtD.pt) = true) = true)
    (hc : chk PtD.tn PtD.tq cntP B (L.getD 0 dummyP) (L.drop 1) = true) :
    (∀ t, (n0 : ℝ) / 2 ^ q0 ≤ t → t < (n1 : ℝ) / 2 ^ q1 → Good t) ∧
      P ((n0 : ℝ) / 2 ^ q0) (K + B) := by
  simp only [decide_eq_true_eq] at hf
  obtain ⟨e0, e1, e3, e4, hne, hch⟩ := hf
  obtain ⟨a, l, rfl⟩ : ∃ a l, L = a :: l := List.exists_cons_of_ne_nil hne
  simp only [List.getD_cons_zero, List.drop_succ_cons, List.drop_zero] at e0 e1 e3 hc
  subst e0 e1 e4
  have hlast : ((RS5.lastOf a l).tn : ℝ) / 2 ^ (RS5.lastOf a l).tq ≤ (n1 : ℝ) / 2 ^ q1 :=
    hle_of e3
  have hQ : QP (a :: l) := ⟨hall, hch⟩
  exact ⟨eng PtD.tn PtD.tq cntP QP QP_tail QP_band B _ hP h6 l a hQ hlast hc,
    engP PtD.tn PtD.tq cntP QP QP_band B _ hP h6 l a hQ hlast hc⟩

end ZC
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Arb4 Arb4.H1000 H1000Line

namespace ZC

theorem bridgeP : P (((34078720 : ℕ) : ℝ) / 2 ^ 16) 85005 := by
  obtain ⟨s, hs, hx⟩ := ZeroCount.grid_bridge.2
  have e : (((34078720 : ℕ) : ℝ) / 2 ^ 16) = 520 := by norm_num
  rw [e]
  exact ⟨s, hs, hx⟩

noncomputable def B05short : List PtD := B05_0 ++ B05_1 ++ B05_2 ++ B05_3.take 3
theorem B05last_checked : (B05_3.take 3).all (fun d => ptCheckC d.pt) = true := by
  apply List.all_eq_true.mpr
  intro d hd
  exact List.all_eq_true.mp B05_3_ok d (List.mem_of_mem_take hd)
theorem B05short_checked : B05short.all (fun d => ptCheckC d.pt) = true := by
  exact allC_append (allC_append (allC_append B05_0_ok B05_1_ok) B05_2_ok) B05last_checked

end ZC
open ZC
namespace ZC.GridB
theorem all_B12 : (B12).all (fun d => ptCheckC d.pt) = true := by
  rw [show B12 = B12_0 ++ (B12_1 ++ (B12_2 ++ B12_3)) from rfl]
  exact allC_append B12_0_ok (allC_append B12_1_ok (allC_append B12_2_ok B12_3_ok))
theorem s_B12 : (∀ t, (((492544 : ℕ) : ℝ) / 2 ^ 10) ≤ t → t < (((34078720 : ℕ) : ℝ) / 2 ^ 16) → Good t) ∧ P (((492544 : ℕ) : ℝ) / 2 ^ 10) 85032 :=
  ptStep (B12) 492544 10 34078720 16 27 85005 bridgeP (by norm_num) all_B12 (by decide +kernel) (by decide +kernel)
theorem all_B11 : (B11).all (fun d => ptCheckC d.pt) = true := by
  rw [show B11 = B11_0 ++ (B11_1 ++ (B11_2 ++ B11_3)) from rfl]
  exact allC_append B11_0_ok (allC_append B11_1_ok (allC_append B11_2_ok B11_3_ok))
theorem s_B11 : (∀ t, (((451584 : ℕ) : ℝ) / 2 ^ 10) ≤ t → t < (((492544 : ℕ) : ℝ) / 2 ^ 10) → Good t) ∧ P (((451584 : ℕ) : ℝ) / 2 ^ 10) 85059 :=
  ptStep (B11) 451584 10 492544 10 27 85032 s_B12.2 (by norm_num) all_B11 (by decide +kernel) (by decide +kernel)
theorem all_B10 : (B10).all (fun d => ptCheckC d.pt) = true := by
  rw [show B10 = B10_0 ++ (B10_1 ++ (B10_2 ++ B10_3)) from rfl]
  exact allC_append B10_0_ok (allC_append B10_1_ok (allC_append B10_2_ok B10_3_ok))
theorem s_B10 : (∀ t, (((410624 : ℕ) : ℝ) / 2 ^ 10) ≤ t → t < (((451584 : ℕ) : ℝ) / 2 ^ 10) → Good t) ∧ P (((410624 : ℕ) : ℝ) / 2 ^ 10) 85086 :=
  ptStep (B10) 410624 10 451584 10 27 85059 s_B11.2 (by norm_num) all_B10 (by decide +kernel) (by decide +kernel)
theorem all_B09 : (B09).all (fun d => ptCheckC d.pt) = true := by
  rw [show B09 = B09_0 ++ (B09_1 ++ (B09_2 ++ B09_3)) from rfl]
  exact allC_append B09_0_ok (allC_append B09_1_ok (allC_append B09_2_ok B09_3_ok))
theorem s_B09 : (∀ t, (((369664 : ℕ) : ℝ) / 2 ^ 10) ≤ t → t < (((410624 : ℕ) : ℝ) / 2 ^ 10) → Good t) ∧ P (((369664 : ℕ) : ℝ) / 2 ^ 10) 85112 :=
  ptStep (B09) 369664 10 410624 10 26 85086 s_B10.2 (by norm_num) all_B09 (by decide +kernel) (by decide +kernel)
theorem all_B08 : (B08).all (fun d => ptCheckC d.pt) = true := by
  rw [show B08 = B08_0 ++ (B08_1 ++ (B08_2 ++ B08_3)) from rfl]
  exact allC_append B08_0_ok (allC_append B08_1_ok (allC_append B08_2_ok B08_3_ok))
theorem s_B08 : (∀ t, (((328704 : ℕ) : ℝ) / 2 ^ 10) ≤ t → t < (((369664 : ℕ) : ℝ) / 2 ^ 10) → Good t) ∧ P (((328704 : ℕ) : ℝ) / 2 ^ 10) 85138 :=
  ptStep (B08) 328704 10 369664 10 26 85112 s_B09.2 (by norm_num) all_B08 (by decide +kernel) (by decide +kernel)
theorem all_B07 : (B07).all (fun d => ptCheckC d.pt) = true := by
  rw [show B07 = B07_0 ++ (B07_1 ++ (B07_2 ++ B07_3)) from rfl]
  exact allC_append B07_0_ok (allC_append B07_1_ok (allC_append B07_2_ok B07_3_ok))
theorem s_B07 : (∀ t, (((287744 : ℕ) : ℝ) / 2 ^ 10) ≤ t → t < (((328704 : ℕ) : ℝ) / 2 ^ 10) → Good t) ∧ P (((287744 : ℕ) : ℝ) / 2 ^ 10) 85162 :=
  ptStep (B07) 287744 10 328704 10 24 85138 s_B08.2 (by norm_num) all_B07 (by decide +kernel) (by decide +kernel)
theorem all_B06 : (B06).all (fun d => ptCheckC d.pt) = true := by
  rw [show B06 = B06_0 ++ (B06_1 ++ (B06_2 ++ B06_3)) from rfl]
  exact allC_append B06_0_ok (allC_append B06_1_ok (allC_append B06_2_ok B06_3_ok))
theorem s_B06 : (∀ t, (((246784 : ℕ) : ℝ) / 2 ^ 10) ≤ t → t < (((287744 : ℕ) : ℝ) / 2 ^ 10) → Good t) ∧ P (((246784 : ℕ) : ℝ) / 2 ^ 10) 85186 :=
  ptStep (B06) 246784 10 287744 10 24 85162 s_B07.2 (by norm_num) all_B06 (by decide +kernel) (by decide +kernel)
theorem all_B05 : (B05short).all (fun d => ptCheckC d.pt) = true := B05short_checked
theorem s_B05 : (∀ t, (((205824 : ℕ) : ℝ) / 2 ^ 10) ≤ t → t < (((246784 : ℕ) : ℝ) / 2 ^ 10) → Good t) ∧ P (((205824 : ℕ) : ℝ) / 2 ^ 10) 85209 :=
  ptStep (B05short) 205824 10 246784 10 23 85186 s_B06.2 (by norm_num) all_B05 (by decide +kernel) (by decide +kernel)
theorem all_B04 : (B04).all (fun d => ptCheckC d.pt) = true := by
  rw [show B04 = B04_0 ++ (B04_1 ++ (B04_2 ++ B04_3)) from rfl]
  exact allC_append B04_0_ok (allC_append B04_1_ok (allC_append B04_2_ok B04_3_ok))
theorem s_B04 : (∀ t, (((164864 : ℕ) : ℝ) / 2 ^ 10) ≤ t → t < (((205824 : ℕ) : ℝ) / 2 ^ 10) → Good t) ∧ P (((164864 : ℕ) : ℝ) / 2 ^ 10) 85230 :=
  ptStep (B04) 164864 10 205824 10 21 85209 s_B05.2 (by norm_num) all_B04 (by decide +kernel) (by decide +kernel)
theorem all_B03 : (B03).all (fun d => ptCheckC d.pt) = true := by
  rw [show B03 = B03_0 ++ (B03_1 ++ B03_2) from rfl]
  exact allC_append B03_0_ok (allC_append B03_1_ok B03_2_ok)
theorem s_B03 : (∀ t, (((123904 : ℕ) : ℝ) / 2 ^ 10) ≤ t → t < (((164864 : ℕ) : ℝ) / 2 ^ 10) → Good t) ∧ P (((123904 : ℕ) : ℝ) / 2 ^ 10) 85250 :=
  ptStep (B03) 123904 10 164864 10 20 85230 s_B04.2 (by norm_num) all_B03 (by decide +kernel) (by decide +kernel)
theorem region : (∀ t, (((123904 : ℕ) : ℝ) / 2 ^ 10) ≤ t → t < (((34078720 : ℕ) : ℝ) / 2 ^ 16) → Good t) ∧ P (((123904 : ℕ) : ℝ) / 2 ^ 10) 85250 := by
  refine ⟨fun t h0 h1 => ?_, s_B03.2⟩
  by_cases c0 : t < (((164864 : ℕ) : ℝ) / 2 ^ 10)
  · exact s_B03.1 t (by norm_num at *; linarith) c0
  push Not at c0
  by_cases c1 : t < (((205824 : ℕ) : ℝ) / 2 ^ 10)
  · exact s_B04.1 t (by norm_num at *; linarith) c1
  push Not at c1
  by_cases c2 : t < (((246784 : ℕ) : ℝ) / 2 ^ 10)
  · exact s_B05.1 t (by norm_num at *; linarith) c2
  push Not at c2
  by_cases c3 : t < (((287744 : ℕ) : ℝ) / 2 ^ 10)
  · exact s_B06.1 t (by norm_num at *; linarith) c3
  push Not at c3
  by_cases c4 : t < (((328704 : ℕ) : ℝ) / 2 ^ 10)
  · exact s_B07.1 t (by norm_num at *; linarith) c4
  push Not at c4
  by_cases c5 : t < (((369664 : ℕ) : ℝ) / 2 ^ 10)
  · exact s_B08.1 t (by norm_num at *; linarith) c5
  push Not at c5
  by_cases c6 : t < (((410624 : ℕ) : ℝ) / 2 ^ 10)
  · exact s_B09.1 t (by norm_num at *; linarith) c6
  push Not at c6
  by_cases c7 : t < (((451584 : ℕ) : ℝ) / 2 ^ 10)
  · exact s_B10.1 t (by norm_num at *; linarith) c7
  push Not at c7
  by_cases c8 : t < (((492544 : ℕ) : ℝ) / 2 ^ 10)
  · exact s_B11.1 t (by norm_num at *; linarith) c8
  push Not at c8
  exact s_B12.1 t (by norm_num at *; linarith) h1
end ZC.GridB
theorem solution :
    (∀ t : ℝ, 121 ≤ t → t < 520 →
      ∃ s : Finset ℝ, (85288 : ℝ) - s.card ≤
          t / (2 * Real.pi) * (Real.log (t / (2 * Real.pi)) - 1) + 5 / 2 ∧
        ∀ x ∈ s, t < x ∧ x ≤ 65000 ∧ riemannZeta (1 / 2 + (x : ℂ) * Complex.I) = 0) ∧
    (∃ s : Finset ℝ, s.card = 85250 ∧
      ∀ x ∈ s, 121 < x ∧ x ≤ 65000 ∧
        riemannZeta (1 / 2 + (x : ℂ) * Complex.I) = 0) := by
  obtain ⟨h1, h2⟩ := ZC.GridB.region
  have e0 : (((123904 : ℕ) : ℝ) / 2 ^ 10) = 121 := by norm_num
  have e1 : (((34078720 : ℕ) : ℝ) / 2 ^ 16) = 520 := by norm_num
  rw [e0, e1] at h1
  rw [e0] at h2
  exact ⟨h1, h2⟩
