-- Prove2me | solution 1 for ServiceParts.Allocation.allocOpt_correct
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-04T08:33:24.384237+00:00
-- url     : https://prove2.me/submissions/fc0e0f7d-1c6f-475b-926a-0349891ed32c

import Mathlib
import Theorems.Thm_ServiceParts_Allocation_slope_monotone
import Definitions.Def_ServiceParts_Allocation_AllocOpt

/-
Formalization of Muckstadt (2005), Proposition 2, correctness half.
The definitions are by mikedeng1. The imported slope monotonicity theorem
was proved by Nickrobbins95 (submission 8e35ccbf-47ac-4fd9-b079-e9318ca6a99d).
The proof below establishes the block algorithm's supporting-price invariant.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace ServiceParts.Allocation.AllocOptProof

variable {M : ℕ} (d : AllocData M) (hd : d.WellFormed)

def g (m : Fin M) (k : ℕ) : ℝ := d.grid m k

include hd in
lemma grid_mono (m : Fin M) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ d.n m) :
    d.grid m a ≤ d.grid m b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst a
    rfl
  | succ b ih =>
    by_cases h : a ≤ b
    · exact (ih h (by omega)).trans (le_of_lt (hd.grid_strictMono m b (by omega)))
    · have : a = b + 1 := by omega
      subst a
      rfl

include hd in
lemma g_mono (m : Fin M) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ d.n m) :
    g d m a ≤ g d m b := by
  dsimp [g]
  exact_mod_cast grid_mono d hd m hab hb

include hd in
lemma g_nonneg (m : Fin M) {k : ℕ} (hk : k ≤ d.n m) : 0 ≤ g d m k := by
  have h := g_mono d hd m (Nat.zero_le k) hk
  simpa [g, hd.grid_zero] using h

include hd in
lemma slope_mono (m : Fin M) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ d.n m) :
    d.slope m a ≤ d.slope m b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst a
    rfl
  | succ b ih =>
    by_cases h : a ≤ b
    · exact (ih h (by omega)).trans (slope_monotone d hd m b (by omega))
    · have : a = b + 1 := by omega
      subst a
      rfl

def seg (a b r : ℝ) : ℝ := min r b - min r a

lemma seg_mono {a b r t : ℝ} (hab : a ≤ b) (hrt : r ≤ t) :
    seg a b r ≤ seg a b t := by
  unfold seg
  simp only [min_def]
  split_ifs <;> linarith

lemma tail_mono {b r t : ℝ} (hrt : r ≤ t) : r - min r b ≤ t - min t b := by
  simp only [min_def]
  split_ifs <;> linarith

lemma segment_formula {a b r : ℝ} (hab : a ≤ b) :
    (if a ≤ r then (min r b - a) else 0) = seg a b r := by
  unfold seg
  by_cases h : a ≤ r
  · simp [h]
  · have hr : r ≤ a := le_of_lt (lt_of_not_ge h)
    simp [h, min_eq_left hr, min_eq_left (hr.trans hab)]

lemma tail_formula (b r : ℝ) :
    (if b ≤ r then r - b else 0) = r - min r b := by
  by_cases h : b ≤ r
  · simp [h]
  · simp [h, min_eq_left (le_of_lt (lt_of_not_ge h))]

include hd in
lemma pwl_formula (m : Fin M) (r : ℝ) :
    d.pwl m r = d.cost m 0 +
      (∑ j ∈ Finset.range (d.n m), seg (g d m j) (g d m (j+1)) r * d.slope m j) +
      (r - min r (g d m (d.n m))) * d.slope m (d.n m) := by
  unfold AllocData.pwl
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hgj := g_mono d hd m (Nat.le_succ j) (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
    have := segment_formula (r := r) hgj
    have hp := congrArg (fun z => z * d.slope m j) this
    dsimp [g] at hp ⊢
    by_cases h : (d.grid m j : ℝ) ≤ r <;> simpa [h] using hp
  · have := tail_formula (g d m (d.n m)) r
    have hp := congrArg (fun z => z * d.slope m (d.n m)) this
    dsimp [g] at hp ⊢
    by_cases h : (d.grid m (d.n m) : ℝ) ≤ r
    · simp [h]
    · simp [h, min_eq_left (le_of_lt (lt_of_not_ge h))]

lemma seg_sum (m : Fin M) (r : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, seg (g d m j) (g d m (j+1)) r) =
      min r (g d m n) - min r (g d m 0) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; unfold seg; ring

include hd in
lemma pwl_zero (m : Fin M) : d.pwl m 0 = d.cost m 0 := by
  rw [pwl_formula d hd]
  have hg : ∀ j, j ≤ d.n m → min (0 : ℝ) (g d m j) = 0 :=
    fun j hj => min_eq_left (g_nonneg d hd m hj)
  simp only [seg]
  rw [show (∑ j ∈ Finset.range (d.n m),
      (min 0 (g d m (j+1)) - min 0 (g d m j)) * d.slope m j) = 0 by
    apply Finset.sum_eq_zero
    intro j hj
    have hj := Finset.mem_range.mp hj
    rw [hg (j+1) (by omega), hg j (by omega)]
    ring]
  rw [hg (d.n m) (by rfl)]
  ring

def delta (m : Fin M) (j : ℕ) (r t : ℝ) : ℝ :=
  seg (g d m j) (g d m (j+1)) t - seg (g d m j) (g d m (j+1)) r

def tailDelta (m : Fin M) (r t : ℝ) : ℝ :=
  (t - min t (g d m (d.n m))) - (r - min r (g d m (d.n m)))

include hd in
lemma delta_total (m : Fin M) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) :
    (∑ j ∈ Finset.range (d.n m), delta d m j r t) + tailDelta d m r t = t - r := by
  unfold delta tailDelta
  rw [Finset.sum_sub_distrib, seg_sum, seg_sum]
  simp only [g, hd.grid_zero, Int.cast_zero, min_eq_right hr, min_eq_right ht]
  ring

include hd in
lemma pwl_sub (m : Fin M) (r t : ℝ) :
    d.pwl m t - d.pwl m r =
      (∑ j ∈ Finset.range (d.n m), delta d m j r t * d.slope m j) +
      tailDelta d m r t * d.slope m (d.n m) := by
  rw [pwl_formula d hd, pwl_formula d hd]
  simp only [delta, tailDelta, sub_mul, Finset.sum_sub_distrib]
  ring

include hd in
lemma delta_nonneg (m : Fin M) {j : ℕ} (hj : j < d.n m) {r t : ℝ} (hrt : r ≤ t) :
    0 ≤ delta d m j r t :=
  sub_nonneg.mpr (seg_mono (g_mono d hd m (Nat.le_succ j) (by omega)) hrt)

include hd in
lemma delta_before (m : Fin M) {j k : ℕ} (hjk : j < k) (hk : k ≤ d.n m)
    {r t : ℝ} (hr : g d m k ≤ r) (hrt : r ≤ t) : delta d m j r t = 0 := by
  have h1 : g d m (j+1) ≤ r := (g_mono d hd m (by omega) hk).trans hr
  have h0 : g d m j ≤ r := (g_mono d hd m (by omega) hk).trans hr
  simp [delta, seg, min_eq_right h1, min_eq_right h0,
    min_eq_right (h1.trans hrt), min_eq_right (h0.trans hrt)]

include hd in
lemma delta_above (m : Fin M) {j : ℕ} (hj : j < d.n m)
    {r t : ℝ} (hrt : r ≤ t) (ht : t ≤ g d m j) : delta d m j r t = 0 := by
  have ht1 := ht.trans (g_mono d hd m (Nat.le_succ j) (by omega))
  simp [delta, seg, min_eq_left ht, min_eq_left ht1,
    min_eq_left (hrt.trans ht), min_eq_left (hrt.trans ht1)]

lemma tailDelta_below (m : Fin M) {r t : ℝ} (hrt : r ≤ t)
    (ht : t ≤ g d m (d.n m)) : tailDelta d m r t = 0 := by
  simp [tailDelta, min_eq_left ht, min_eq_left (hrt.trans ht)]

include hd in
lemma pwl_right (m : Fin M) {k : ℕ} (hk : k ≤ d.n m) {r t : ℝ}
    (hr : g d m k ≤ r) (hrt : r ≤ t) :
    d.pwl m r + d.slope m k * (t-r) ≤ d.pwl m t := by
  have hr0 : 0 ≤ r := (g_nonneg d hd m hk).trans hr
  have hsum :
      (∑ j ∈ Finset.range (d.n m), delta d m j r t * d.slope m k) ≤
      (∑ j ∈ Finset.range (d.n m), delta d m j r t * d.slope m j) := by
    apply Finset.sum_le_sum
    intro j hj
    by_cases hjk : j < k
    · simp [delta_before d hd m hjk hk hr hrt]
    · exact mul_le_mul_of_nonneg_left
        (slope_mono d hd m (by omega) (Nat.le_of_lt (Finset.mem_range.mp hj)))
        (delta_nonneg d hd m (Finset.mem_range.mp hj) hrt)
  have htail : tailDelta d m r t * d.slope m k ≤
      tailDelta d m r t * d.slope m (d.n m) :=
    mul_le_mul_of_nonneg_left (slope_mono d hd m hk le_rfl)
      (sub_nonneg.mpr (tail_mono hrt))
  have h := add_le_add hsum htail
  rw [← pwl_sub d hd, ← Finset.sum_mul, ← add_mul, delta_total d hd m hr0 (hr0.trans hrt)] at h
  nlinarith

include hd in
lemma pwl_affine (m : Fin M) {k : ℕ} (hk : k ≤ d.n m) {r t : ℝ}
    (hr : g d m k ≤ r) (hrt : r ≤ t)
    (ht : k < d.n m → t ≤ g d m (k+1)) :
    d.pwl m t = d.pwl m r + d.slope m k * (t-r) := by
  have hr0 : 0 ≤ r := (g_nonneg d hd m hk).trans hr
  have hsum :
      (∑ j ∈ Finset.range (d.n m), delta d m j r t * d.slope m j) =
      (∑ j ∈ Finset.range (d.n m), delta d m j r t * d.slope m k) := by
    apply Finset.sum_congr rfl
    intro j hj
    rcases lt_trichotomy j k with hjk | rfl | hkj
    · simp [delta_before d hd m hjk hk hr hrt]
    · rfl
    · have hkn : k < d.n m := lt_trans hkj (Finset.mem_range.mp hj)
      have htg : t ≤ g d m j :=
        (ht hkn).trans (g_mono d hd m (by omega) (Nat.le_of_lt (Finset.mem_range.mp hj)))
      simp [delta_above d hd m (Finset.mem_range.mp hj) hrt htg]
  have htail : tailDelta d m r t * d.slope m (d.n m) =
      tailDelta d m r t * d.slope m k := by
    by_cases hkn : k < d.n m
    · have htg := (ht hkn).trans (g_mono d hd m (by omega) le_rfl)
      simp [tailDelta_below d m hrt htg]
    · have : k = d.n m := by omega
      rw [this]
  have h := pwl_sub d hd m r t
  rw [hsum, htail, ← Finset.sum_mul, ← add_mul, delta_total d hd m hr0 (hr0.trans hrt)] at h
  nlinarith

noncomputable def price (s : AllocState M) : ℝ := d.slope s.mStar (s.nStar s.mStar)

/-- A feasible segment representation, its exact cost, and a common supporting price. -/
structure Inv (s : AllocState M) : Prop where
  idx : ∀ m, s.nStar m ≤ d.n m
  lo : ∀ m, d.grid m (s.nStar m) ≤ s.rStar m
  hi : ∀ m, s.nStar m < d.n m → s.rStar m < d.grid m (s.nStar m + 1)
  argmin : ∀ m, price d s ≤ d.slope m (s.nStar m)
  cost : s.z = ∑ m, d.pwl m (s.rStar m)
  support : ∀ m t, 0 ≤ t →
    d.pwl m (s.rStar m) + price d s * (t - s.rStar m) ≤ d.pwl m t

include hd in
lemma inv_nonneg {s : AllocState M} (hs : Inv d s) (m : Fin M) : 0 ≤ s.rStar m := by
  have h := grid_mono d hd m (Nat.zero_le (s.nStar m)) (hs.idx m)
  rw [hd.grid_zero] at h
  exact h.trans (hs.lo m)

include hd in
lemma raise_support (m : Fin M) {k : ℕ} (hk : k ≤ d.n m) {r p q : ℝ}
    (hr : g d m k ≤ r) (hpq : p ≤ q) (hq : q ≤ d.slope m k)
    (hp : ∀ t, 0 ≤ t → d.pwl m r + p * (t-r) ≤ d.pwl m t) :
    ∀ t, 0 ≤ t → d.pwl m r + q * (t-r) ≤ d.pwl m t := by
  intro t ht
  by_cases htr : t ≤ r
  · have h := mul_le_mul_of_nonpos_right hpq (sub_nonpos.mpr htr)
    linarith [hp t ht]
  · have hrt : r ≤ t := le_of_lt (lt_of_not_ge htr)
    have h := mul_le_mul_of_nonneg_right hq (sub_nonneg.mpr hrt)
    linarith [pwl_right d hd m hk hr hrt]

variable (sel : (Fin M → ℝ) → Fin M) (hsel : IsArgminRule sel)

include hd hsel in
lemma inv_init : Inv d (d.initState sel) := by
  constructor
  · intro m; exact Nat.zero_le _
  · intro m; change d.grid m 0 ≤ 0; rw [hd.grid_zero]
  · intro m hm
    change (0 : ℤ) < d.grid m (0+1)
    have h := hd.grid_strictMono m 0 hm
    simpa [hd.grid_zero] using h
  · intro m
    exact hsel (d.currentSlopes fun _ => 0) m
  · simp only [AllocData.initState, Int.cast_zero]
    simp_rw [pwl_zero d hd]
  · intro m t ht
    simp only [AllocData.initState, price, Int.cast_zero]
    have hp : d.slope (sel (d.currentSlopes fun _ => 0)) 0 ≤ d.slope m 0 :=
      hsel (d.currentSlopes fun _ => 0) m
    have h := pwl_right d hd m (Nat.zero_le (d.n m))
      (r := 0) (t := t) (by simp [g, hd.grid_zero]) ht
    nlinarith [mul_le_mul_of_nonneg_right hp ht]

def blockIndex (s : AllocState M) (x : ℤ) : ℕ :=
  if s.nStar s.mStar < d.n s.mStar ∧
      s.rStar s.mStar + x = d.grid s.mStar (s.nStar s.mStar+1)
  then s.nStar s.mStar + 1 else s.nStar s.mStar

noncomputable def blockState (s : AllocState M) (x : ℤ) : AllocState M :=
  let ns := Function.update s.nStar s.mStar (blockIndex d s x)
  { nStar := ns
    rStar := Function.update s.rStar s.mStar (s.rStar s.mStar+x)
    mStar := sel (d.currentSlopes ns)
    z := s.z + (x : ℝ) * price d s
    u := s.u - x }

include hd hsel in
lemma inv_block {s : AllocState M} (hs : Inv d s) {x : ℤ} (hx : 0 ≤ x)
    (hbound : s.nStar s.mStar < d.n s.mStar →
      s.rStar s.mStar + x ≤ d.grid s.mStar (s.nStar s.mStar+1)) :
    Inv d (blockState d sel s x) := by
  let ns := Function.update s.nStar s.mStar (blockIndex d s x)
  let rs := Function.update s.rStar s.mStar (s.rStar s.mStar+x)
  have hki : s.nStar s.mStar ≤ blockIndex d s x := by
    unfold blockIndex
    split_ifs <;> omega
  have hkn : blockIndex d s x ≤ d.n s.mStar := by
    unfold blockIndex
    split_ifs with h
    · omega
    · exact hs.idx s.mStar
  have hidx : ∀ m, ns m ≤ d.n m := by
    intro m
    by_cases hm : m = s.mStar
    · subst m; simpa [ns] using hkn
    · simpa [ns, hm] using hs.idx m
  have hlo : ∀ m, d.grid m (ns m) ≤ rs m := by
    intro m
    by_cases hm : m = s.mStar
    · subst m
      simp only [ns, rs, Function.update_self]
      unfold blockIndex
      split_ifs with h
      · omega
      · exact (hs.lo s.mStar).trans (le_add_of_nonneg_right hx)
    · simpa [ns, rs, hm] using hs.lo m
  have hhi : ∀ m, ns m < d.n m → rs m < d.grid m (ns m+1) := by
    intro m hm
    by_cases heq : m = s.mStar
    · subst m
      simp only [ns, rs, Function.update_self] at hm ⊢
      unfold blockIndex at hm ⊢
      split_ifs with h
      · simp only [if_pos h] at hm
        have hg := hd.grid_strictMono s.mStar (s.nStar s.mStar+1) hm
        omega
      · simp only [if_neg h] at hm
        have hb := hbound hm
        omega
    · simpa [ns, rs, heq] using hs.hi m (by simpa [ns, heq] using hm)
  have hnewge : ∀ m, price d s ≤ d.slope m (ns m) := by
    intro m
    by_cases hm : m = s.mStar
    · subst m
      simp only [ns, Function.update_self]
      exact slope_mono d hd s.mStar hki hkn
    · simpa [ns, hm] using hs.argmin m
  have hprice : price d s ≤ price d (blockState d sel s x) :=
    hnewge (sel (d.currentSlopes ns))
  have harg : ∀ m, price d (blockState d sel s x) ≤ d.slope m (ns m) :=
    hsel (d.currentSlopes ns)
  have hcostm : d.pwl s.mStar (s.rStar s.mStar+x) =
      d.pwl s.mStar (s.rStar s.mStar) + (x : ℝ) * price d s := by
    have h := pwl_affine d hd s.mStar (hs.idx s.mStar)
      (r := (s.rStar s.mStar : ℝ)) (t := ((s.rStar s.mStar+x : ℤ) : ℝ))
      (by dsimp [g]; exact_mod_cast hs.lo s.mStar) (by exact_mod_cast (show s.rStar s.mStar ≤ s.rStar s.mStar+x by omega))
      (fun hk => by dsimp [g]; exact_mod_cast hbound hk)
    push_cast at h ⊢
    dsimp [price]
    nlinarith
  have hcostpoint : ∀ m, d.pwl m (rs m) =
      d.pwl m (s.rStar m) + if m = s.mStar then (x : ℝ) * price d s else 0 := by
    intro m
    by_cases hm : m = s.mStar
    · subst m; simpa [rs] using hcostm
    · simp [rs, hm]
  have hcost : (blockState d sel s x).z = ∑ m, d.pwl m (rs m) := by
    simp_rw [hcostpoint]
    rw [Finset.sum_add_distrib]
    simp [blockState, hs.cost]
  have hsupp : ∀ m t, 0 ≤ t →
      d.pwl m (rs m) + price d s * (t - rs m) ≤ d.pwl m t := by
    intro m t ht
    by_cases hm : m = s.mStar
    · subst m
      simp only [rs, Function.update_self, hcostm, Int.cast_add]
      nlinarith [hs.support s.mStar t ht]
    · simpa [rs, hm] using hs.support m t ht
  refine ⟨hidx, hlo, hhi, harg, hcost, ?_⟩
  intro m t ht
  exact raise_support d hd m (hidx m) (by dsimp [g]; exact_mod_cast hlo m)
    hprice (harg m) (hsupp m) t ht

def amount (s : AllocState M) : ℤ :=
  if s.nStar s.mStar = d.n s.mStar then s.u
  else min s.u (d.grid s.mStar (s.nStar s.mStar+1) - s.rStar s.mStar)

lemma amount_pos {s : AllocState M} (hs : Inv d s) (hu : 0 < s.u) :
    0 < amount d s := by
  unfold amount
  split_ifs with h
  · exact hu
  · have hk := hs.idx s.mStar
    have hg := hs.hi s.mStar (by omega)
    exact lt_min hu (by omega)

lemma amount_le (s : AllocState M) : amount d s ≤ s.u := by
  unfold amount
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

lemma amount_bound (s : AllocState M) (hk : s.nStar s.mStar < d.n s.mStar) :
    s.rStar s.mStar + amount d s ≤ d.grid s.mStar (s.nStar s.mStar+1) := by
  simp only [amount, if_neg (Nat.ne_of_lt hk)]
  have h := min_le_right s.u (d.grid s.mStar (s.nStar s.mStar+1) - s.rStar s.mStar)
  omega

lemma index_update (s : AllocState M) (x : ℤ) :
    (if s.nStar s.mStar < d.n s.mStar ∧
        s.rStar s.mStar+x = d.grid s.mStar (s.nStar s.mStar+1)
      then Function.update s.nStar s.mStar (s.nStar s.mStar+1) else s.nStar) =
    Function.update s.nStar s.mStar (blockIndex d s x) := by
  unfold blockIndex
  split_ifs <;> simp

lemma innerStep_eq (s : AllocState M) :
    d.innerStep sel s = blockState d sel s (amount d s) := by
  simp only [AllocData.innerStep, Function.update_self]
  change
    { nStar := if s.nStar s.mStar < d.n s.mStar ∧
          s.rStar s.mStar+amount d s = d.grid s.mStar (s.nStar s.mStar+1)
        then Function.update s.nStar s.mStar (s.nStar s.mStar+1) else s.nStar
      rStar := Function.update s.rStar s.mStar (s.rStar s.mStar+amount d s)
      mStar := _
      z := s.z+(amount d s : ℝ)*price d s
      u := s.u-amount d s } = blockState d sel s (amount d s)
  simp only [index_update]
  rfl

include hd hsel in
lemma inv_step {s : AllocState M} (hs : Inv d s) (hu : 0 < s.u) :
    Inv d (d.innerStep sel s) := by
  rw [innerStep_eq]
  exact inv_block d hd sel hsel hs (le_of_lt (amount_pos d hs hu)) (amount_bound d s)

lemma step_sum (s : AllocState M) :
    (∑ m, (d.innerStep sel s).rStar m) + (d.innerStep sel s).u =
      (∑ m, s.rStar m) + s.u := by
  rw [innerStep_eq]
  have hp : ∀ m, (blockState d sel s (amount d s)).rStar m =
      s.rStar m + if m = s.mStar then amount d s else 0 := by
    intro m
    by_cases hm : m = s.mStar <;> simp [blockState, hm]
  simp_rw [hp]
  rw [Finset.sum_add_distrib]
  simp [blockState]

include hd hsel in
lemma inv_loop (budget : ℕ) (s : AllocState M) (hs : Inv d s)
    (hu : 0 ≤ s.u) (hb : s.u.toNat ≤ budget) :
    Inv d (d.innerLoop sel false budget s) ∧
      (d.innerLoop sel false budget s).u = 0 ∧
      (∑ m, (d.innerLoop sel false budget s).rStar m) = (∑ m, s.rStar m) + s.u := by
  induction budget generalizing s with
  | zero =>
    have hz : s.u = 0 := by omega
    simpa [AllocData.innerLoop, hz] using hs
  | succ budget ih =>
    by_cases hpos : 0 < s.u
    · have hx := amount_pos d hs hpos
      have hxu := amount_le d s
      have hun : 0 ≤ (d.innerStep sel s).u := by
        rw [innerStep_eq]
        change 0 ≤ s.u - amount d s
        omega
      have hbn : (d.innerStep sel s).u.toNat ≤ budget := by
        rw [innerStep_eq]
        change (s.u - amount d s).toNat ≤ budget
        omega
      obtain ⟨hi, hz, hr⟩ := ih (d.innerStep sel s) (inv_step d hd sel hsel hs hpos) hun hbn
      simp only [AllocData.innerLoop, hpos, true_or, and_self, ↓reduceIte]
      exact ⟨hi, hz, hr.trans (step_sum d sel s)⟩
    · have hz : s.u = 0 := by omega
      simpa [AllocData.innerLoop, hz] using hs

lemma inv_set_u {s : AllocState M} (hs : Inv d s) (u : ℤ) :
    Inv d { s with u := u } :=
  ⟨hs.idx, hs.lo, hs.hi, hs.argmin, hs.cost, hs.support⟩

include hd hsel in
lemma inv_outer (k : ℕ) (hk : k ≤ d.n0) :
    Inv d (d.stateAfter sel false k) ∧
      (d.stateAfter sel false k).u = 0 ∧
      (∑ m, (d.stateAfter sel false k).rStar m) = d.grid0 k := by
  induction k with
  | zero =>
    refine ⟨inv_init d hd sel hsel, rfl, ?_⟩
    simp [AllocData.stateAfter, AllocData.initState, hd.grid0_zero]
  | succ k ih =>
    obtain ⟨hs, hu, hr⟩ := ih (by omega)
    let s : AllocState M := { d.stateAfter sel false k with u := d.grid0 (k+1)-d.grid0 k }
    have hsu : 0 ≤ s.u := by
      have h := hd.grid0_strictMono k (by omega)
      dsimp [s]
      omega
    obtain ⟨hi, hz, hr'⟩ := inv_loop d hd sel hsel
      (s.u.toNat + ∑ m, d.n m + 1) s (inv_set_u d hs _) hsu (by omega)
    refine ⟨hi, hz, ?_⟩
    change (∑ m, (d.innerLoop sel false (s.u.toNat + ∑ m, d.n m + 1) s).rStar m) = _
    rw [hr']
    change (∑ m, (d.stateAfter sel false k).rStar m) +
      (d.grid0 (k+1)-d.grid0 k) = _
    rw [hr]
    omega

end ServiceParts.Allocation.AllocOptProof

open ServiceParts.Allocation ServiceParts.Allocation.AllocOptProof in
/-- AllocOpt attains the minimum cost among all nonnegative integer allocations
with the specified total. The proof uses a common supporting price preserved
by each block allocation. -/
theorem solution {Mbar : ℕ} (d : AllocData Mbar) (hd : d.WellFormed)
    (sel : (Fin Mbar → ℝ) → Fin Mbar) (hsel : IsArgminRule sel)
    (k : ℕ) (hk : k ≤ d.n0) :
    (∃ r : Fin Mbar → ℕ, ∑ m, (r m : ℤ) = d.grid0 k ∧
        d.allocOpt sel k = d.f (d.grid0 k) + ∑ m, d.pwl m (r m)) ∧
      ∀ r : Fin Mbar → ℕ, ∑ m, (r m : ℤ) = d.grid0 k →
        d.allocOpt sel k ≤ d.f (d.grid0 k) + ∑ m, d.pwl m (r m) := by
  let s := d.stateAfter sel false k
  obtain ⟨hs, _, hr⟩ := inv_outer d hd sel hsel k hk
  have hs : Inv d s := hs
  have hr : (∑ m, s.rStar m) = d.grid0 k := hr
  have hc : d.allocOpt sel k = d.f (d.grid0 k) + ∑ m, d.pwl m (s.rStar m) := by
    change s.z + d.f (d.grid0 k) = _
    rw [hs.cost]
    ring
  constructor
  · have hcast : ∀ m, ((s.rStar m).toNat : ℤ) = s.rStar m :=
      fun m => Int.toNat_of_nonneg (inv_nonneg d hd hs m)
    have hcastR : ∀ m, ((s.rStar m).toNat : ℝ) = (s.rStar m : ℝ) := by
      intro m
      exact_mod_cast hcast m
    refine ⟨fun m => (s.rStar m).toNat, ?_, ?_⟩
    · simpa only [hcast] using hr
    · simpa only [hcastR] using hc
  · intro r htotal
    have hsR : (∑ m, (s.rStar m : ℝ)) = (d.grid0 k : ℝ) := by exact_mod_cast hr
    have hrR : (∑ m, (r m : ℝ)) = (d.grid0 k : ℝ) := by exact_mod_cast htotal
    have hdiff : (∑ m, ((r m : ℝ) - (s.rStar m : ℝ))) = 0 := by
      rw [Finset.sum_sub_distrib, hrR, hsR]
      ring
    have hsum := Finset.sum_le_sum (s := Finset.univ)
      (fun m _ => hs.support m (r m) (Nat.cast_nonneg _))
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hdiff, mul_zero, add_zero] at hsum
    rw [hc]
    linarith
