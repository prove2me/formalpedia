-- Prove2me | solution 1 for SolomonRWRE.Recurrence.lemma_1_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T05:47:36.55603+00:00
-- url     : https://prove2.me/submissions/d6487678-3011-4368-8d2d-64f4c9cf81e4

import Mathlib
import Definitions.Def_SolomonRWRE_Recurrence_Model

set_option autoImplicit false

open scoped ENNReal

namespace SpitzerLib

/-! ### Deterministic part: ladder epochs and the cyclic (Feller XII.6) lemma -/

/-- partial sums `s x n = x 0 + ⋯ + x (n-1)` -/
def s (x : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, x j

/-- `n` is a strict ascending ladder epoch (vacuous for `n = 0`) -/
def isL (x : ℕ → ℝ) (n : ℕ) : Prop := ∀ m < n, s x m < s x n

open Classical in
/-- number of strict ascending ladder epochs in `[1, n]` -/
noncomputable def cnt (x : ℕ → ℝ) (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter (fun j => isL x j)).card

/-- index map of the `i`-th cyclic rotation of the first `n` coordinates -/
def g (n i j : ℕ) : ℕ := if j < n then (i + j) % n else j

/-- `i`-th cyclic rotation of the first `n` coordinates of `x` -/
def rot (x : ℕ → ℝ) (n i : ℕ) : ℕ → ℝ := fun j => x (g n i j)

lemma g_injective (n i : ℕ) : Function.Injective (g n i) := by
  intro a b h
  unfold g at h
  split_ifs at h with ha hb hb
  · have h1 : (i + a) ≡ (i + b) [MOD n] := h
    have h2 : a ≡ b [MOD n] := Nat.ModEq.add_left_cancel' i h1
    exact Nat.ModEq.eq_of_lt_of_lt h2 ha hb
  · have := Nat.mod_lt (i + a) (show 0 < n by omega)
    omega
  · have := Nat.mod_lt (i + b) (show 0 < n by omega)
    omega
  · exact h

/-- periodic extension of the partial sums -/
def ps (x : ℕ → ℝ) (n t : ℕ) : ℝ := ∑ u ∈ Finset.range t, x (u % n)

lemma ps_succ (x : ℕ → ℝ) (n t : ℕ) : ps x n (t + 1) = ps x n t + x (t % n) := by
  simp [ps, Finset.sum_range_succ]

lemma ps_n (x : ℕ → ℝ) (n : ℕ) : ps x n n = s x n := by
  unfold ps s
  exact Finset.sum_congr rfl (fun u hu => by rw [Nat.mod_eq_of_lt (Finset.mem_range.1 hu)])

lemma ps_lt (x : ℕ → ℝ) (n u : ℕ) (hu : u ≤ n) : ps x n u = s x u := by
  unfold ps s
  exact Finset.sum_congr rfl (fun v hv => by
    rw [Nat.mod_eq_of_lt (by have := Finset.mem_range.1 hv; omega)])

lemma ps_add_n (x : ℕ → ℝ) (n : ℕ) (t : ℕ) : ps x n (t + n) = ps x n t + s x n := by
  induction t with
  | zero => rw [Nat.zero_add, ps_n]; simp [ps]
  | succ t ih =>
    rw [show t + 1 + n = (t + n) + 1 by omega, ps_succ, ih, ps_succ, Nat.add_mod_right]
    ring

lemma s_rot (x : ℕ → ℝ) (n i : ℕ) (m : ℕ) (hm : m ≤ n) :
    s (rot x n i) m = ps x n (i + m) - ps x n i := by
  induction m with
  | zero => simp [s]
  | succ m ih =>
    have ih' := ih (by omega)
    have hg : g n i m = (i + m) % n := by simp [g, show m < n by omega]
    simp only [s, Finset.sum_range_succ] at ih' ⊢
    rw [ih', show i + (m + 1) = (i + m) + 1 by omega, ps_succ, rot, hg]
    ring

/-- the "look-back-`n` record" property of an index `t` -/
def Rec (x : ℕ → ℝ) (n t : ℕ) : Prop := ∀ u, t ≤ u → u < t + n → ps x n u < ps x n (t + n)

lemma isL_rot_iff (x : ℕ → ℝ) (n i j : ℕ) (hj : j ≤ n) :
    isL (rot x n i) j ↔ ∀ l < j, ps x n (i + l) < ps x n (i + j) := by
  unfold isL
  constructor
  · intro h l hl
    have := h l hl
    rw [s_rot x n i l (by omega), s_rot x n i j hj] at this
    linarith
  · intro h l hl
    rw [s_rot x n i l (by omega), s_rot x n i j hj]
    linarith [h l hl]

lemma isL_rot_n_iff (x : ℕ → ℝ) (n i : ℕ) : isL (rot x n i) n ↔ Rec x n i := by
  rw [isL_rot_iff x n i n le_rfl]
  constructor
  · intro h u hu1 hu2
    have := h (u - i) (by omega)
    rwa [show i + (u - i) = u by omega] at this
  · intro h l hl
    exact h (i + l) (by omega) (by omega)

lemma Rec_periodic (x : ℕ → ℝ) (n t : ℕ) : Rec x n (t + n) ↔ Rec x n t := by
  constructor
  · intro h u hu1 hu2
    have := h (u + n) (by omega) (by omega)
    rw [ps_add_n, ps_add_n] at this
    linarith
  · intro h u hu1 hu2
    obtain ⟨v, rfl⟩ : ∃ v, u = v + n := ⟨u - n, by omega⟩
    have := h v (by omega) (by omega)
    rw [ps_add_n, ps_add_n]
    linarith

lemma isL_rot_iff_Rec (x : ℕ → ℝ) (n i : ℕ) (hRec : Rec x n i) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : j ≤ n) : isL (rot x n i) j ↔ Rec x n (i + j) := by
  rw [isL_rot_iff x n i j hj]
  constructor
  · intro h u hu1 hu2
    have h0 := h 0 (by omega)
    rw [Nat.add_zero] at h0
    have e1 := ps_add_n x n i
    have e2 := ps_add_n x n (i + j)
    by_cases hu : u < i + n
    · have := hRec u (by omega) hu
      linarith
    · obtain ⟨v, rfl⟩ : ∃ v, u = v + n := ⟨u - n, by omega⟩
      have := h (v - i) (by omega)
      rw [show i + (v - i) = v by omega] at this
      rw [ps_add_n]
      linarith
  · intro h l hl
    have := h (i + l + n) (by omega) (by omega)
    rw [ps_add_n, ps_add_n] at this
    linarith

lemma card_periodic (n : ℕ) (hn : 0 < n) (Q : ℕ → Prop) [DecidablePred Q]
    (hQ : ∀ t, Q (t + n) ↔ Q t) (a : ℕ) :
    ((Finset.Ico a (a + n)).filter Q).card = ((Finset.range n).filter Q).card := by
  induction a with
  | zero => rw [Finset.range_eq_Ico, Nat.zero_add]
  | succ a ih =>
    rw [← ih, Finset.card_filter, Finset.card_filter]
    have htop := Finset.sum_Ico_succ_top (show a ≤ a + n by omega)
      (fun u => if Q u then 1 else 0)
    have hbot := Finset.sum_eq_sum_Ico_succ_bot (show a < a + n + 1 by omega)
      (fun u => if Q u then 1 else 0)
    have hper : (if Q (a + n) then 1 else 0) = (if Q a then 1 else 0) := by
      by_cases h : Q a
      · rw [if_pos ((hQ a).2 h), if_pos h]
      · rw [if_neg (fun h' => h ((hQ a).1 h')), if_neg h]
    rw [show a + 1 + n = a + n + 1 by omega]
    beta_reduce at htop hbot
    omega

open Classical in
lemma cnt_rot (x : ℕ → ℝ) (n i : ℕ) (hn : 0 < n) (hRec : Rec x n i) :
    cnt (rot x n i) n = ((Finset.range n).filter (fun t => Rec x n t)).card := by
  unfold cnt
  rw [Finset.filter_congr (p := fun j => isL (rot x n i) j) (q := fun j => Rec x n (i + j))
    (fun j hj => by
      rw [Finset.mem_Icc] at hj
      exact isL_rot_iff_Rec x n i hRec j hj.1 hj.2)]
  rw [← card_periodic n hn (fun t => Rec x n t) (Rec_periodic x n) (i + 1)]
  apply Finset.card_nbij' (fun j => i + j) (fun u => u - i)
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq] at hj ⊢
    simp only [Finset.mem_Ico]
    exact ⟨⟨by omega, by omega⟩, hj.2⟩
  · intro u hu
    simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_setOf_eq] at hu ⊢
    simp only [Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [show i + (u - i) = u by omega]
    exact hu.2
  · intro j hj
    simp
  · intro u hu
    simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_setOf_eq] at hu
    simp only
    omega

lemma Rec_pos (x : ℕ → ℝ) (n t : ℕ) (hn : 0 < n) (h : Rec x n t) : 0 < s x n := by
  have := h t le_rfl (by omega)
  rw [ps_add_n] at this
  linarith

lemma exists_Rec (x : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hs : 0 < s x n) :
    ∃ i < n, Rec x n i := by
  have hex : ∃ i, i < n ∧ ∀ l < n, s x l ≤ s x i := by
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.range n) (fun l => s x l)
      ⟨0, Finset.mem_range.2 hn⟩
    exact ⟨i, Finset.mem_range.1 hi, fun l hl => hmax l (Finset.mem_range.2 hl)⟩
  classical
  let i := Nat.find hex
  have hi : i < n ∧ ∀ l < n, s x l ≤ s x i := Nat.find_spec hex
  have hfirst : ∀ l < i, s x l < s x i := by
    intro l hl
    by_contra hcon
    push_neg at hcon
    have hP : l < n ∧ ∀ m < n, s x m ≤ s x l :=
      ⟨by omega, fun m hm => (hi.2 m hm).trans hcon⟩
    exact Nat.find_min hex hl hP
  refine ⟨i, hi.1, ?_⟩
  intro u hu1 hu2
  rw [ps_add_n, ps_lt x n i hi.1.le]
  by_cases hun : u < n
  · rw [ps_lt x n u hun.le]
    linarith [hi.2 u hun]
  · obtain ⟨v, rfl⟩ : ∃ v, u = v + n := ⟨u - n, by omega⟩
    rw [ps_add_n, ps_lt x n v (by omega)]
    linarith [hfirst v (by omega)]

open Classical in
/-- **Cyclic lemma** (Feller II, XII.6, Lemma 1, in counting form). -/
theorem cyclic (x : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    ∑ i ∈ Finset.range n,
        (if isL (rot x n i) n then ((cnt (rot x n i) n : ℝ≥0∞))⁻¹ else 0) =
      if 0 < s x n then 1 else 0 := by
  set R := (Finset.range n).filter (fun t => Rec x n t) with hR
  have hterm : ∀ i ∈ Finset.range n,
      (if isL (rot x n i) n then ((cnt (rot x n i) n : ℝ≥0∞))⁻¹ else 0) =
        if Rec x n i then ((R.card : ℝ≥0∞))⁻¹ else 0 := by
    intro i _
    by_cases h : Rec x n i
    · rw [if_pos ((isL_rot_n_iff x n i).2 h), if_pos h, cnt_rot x n i hn h]
    · rw [if_neg (fun h' => h ((isL_rot_n_iff x n i).1 h')), if_neg h]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, ← hR, nsmul_eq_mul]
  by_cases hs : 0 < s x n
  · rw [if_pos hs]
    obtain ⟨i, hi, hRi⟩ := exists_Rec x n hn hs
    have hne : (R.card : ℝ≥0∞) ≠ 0 := by
      have hmem : i ∈ R := by
        rw [hR, Finset.mem_filter, Finset.mem_range]
        exact ⟨hi, hRi⟩
      have : 0 < R.card := Finset.card_pos.2 ⟨i, hmem⟩
      exact_mod_cast this.ne'
    exact ENNReal.mul_inv_cancel hne (ENNReal.natCast_ne_top _)
  · rw [if_neg hs]
    have : R = ∅ := by
      rw [hR, Finset.filter_eq_empty_iff]
      intro t _ hRt
      exact hs (Rec_pos x n t hn hRt)
    rw [this]
    simp


/-! ### Counting ladder epochs -/

lemma s_congr {x y : ℕ → ℝ} {m : ℕ} (hxy : ∀ j < m, x j = y j) {n : ℕ} (hn : n ≤ m) :
    s x n = s y n :=
  Finset.sum_congr rfl (fun j hj => hxy j (by simp at hj; omega))

lemma isL_congr {x y : ℕ → ℝ} {m : ℕ} (hxy : ∀ j < m, x j = y j) {n : ℕ} (hn : n ≤ m) :
    isL x n ↔ isL y n := by
  unfold isL
  rw [s_congr hxy hn]
  exact forall₂_congr (fun l hl => by rw [s_congr hxy (by omega)])

lemma cnt_congr {x y : ℕ → ℝ} {m : ℕ} (hxy : ∀ j < m, x j = y j) {n : ℕ} (hn : n ≤ m) :
    cnt x n = cnt y n := by
  classical
  unfold cnt
  congr 1
  exact Finset.filter_congr (fun j hj => isL_congr hxy (n := j) (by rw [Finset.mem_Icc] at hj; omega))

lemma cnt_zero (x : ℕ → ℝ) : cnt x 0 = 0 := by
  simp [cnt]

open Classical in
lemma cnt_succ (x : ℕ → ℝ) (n : ℕ) :
    cnt x (n + 1) = cnt x n + if isL x (n + 1) then 1 else 0 := by
  unfold cnt
  rw [show Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) by
    ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rw [Nat.add_zero]

lemma cnt_succ_of (x : ℕ → ℝ) (n : ℕ) (h : isL x (n + 1)) : cnt x (n + 1) = cnt x n + 1 := by
  classical
  rw [cnt_succ, if_pos h]

lemma cnt_succ_of_not (x : ℕ → ℝ) (n : ℕ) (h : ¬ isL x (n + 1)) : cnt x (n + 1) = cnt x n := by
  classical
  rw [cnt_succ, if_neg h, Nat.add_zero]

lemma cnt_mono (x : ℕ → ℝ) : Monotone (cnt x) := by
  classical
  refine monotone_nat_of_le_succ (fun n => ?_)
  rw [cnt_succ]
  omega

lemma exists_ladder_between (x : ℕ → ℝ) (m : ℕ) :
    ∀ n, cnt x m < cnt x n → ∃ l, m < l ∧ l ≤ n ∧ isL x l := by
  intro n
  induction n with
  | zero => intro h; rw [cnt_zero] at h; omega
  | succ n ih =>
    intro h
    by_cases hL : isL x (n + 1)
    · by_cases hm : m < n + 1
      · exact ⟨n + 1, hm, le_rfl, hL⟩
      · exact absurd h (not_lt.2 (cnt_mono x (by omega)))
    · rw [cnt_succ_of_not x n hL] at h
      obtain ⟨l, h1, h2, h3⟩ := ih h
      exact ⟨l, h1, by omega, h3⟩

lemma exists_hit (x : ℕ → ℝ) (k : ℕ) (h : ∃ n, k + 1 ≤ cnt x n) :
    ∃ m, isL x (m + 1) ∧ cnt x (m + 1) = k + 1 := by
  classical
  have hspec := Nat.find_spec h
  have hn0 : Nat.find h ≠ 0 := by
    intro h0; rw [h0, cnt_zero] at hspec; omega
  obtain ⟨m, hm⟩ : ∃ m, Nat.find h = m + 1 := ⟨Nat.find h - 1, by omega⟩
  have hmin : ¬ k + 1 ≤ cnt x m := Nat.find_min h (by omega)
  rw [hm] at hspec
  by_cases hL : isL x (m + 1)
  · refine ⟨m, hL, ?_⟩
    rw [cnt_succ_of x m hL] at hspec ⊢
    omega
  · rw [cnt_succ_of_not x m hL] at hspec
    exact absurd hspec hmin

lemma cnt_lt_of_ladder (x : ℕ → ℝ) {a b : ℕ} (hab : a < b) (hb : isL x b) :
    cnt x a < cnt x b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rw [cnt_succ_of x b' hb]
  have := cnt_mono x (show a ≤ b' by omega)
  omega

/-- `n + 1` is the `(k+1)`-st ladder epoch -/
def T (n k : ℕ) : Set (ℕ → ℝ) := {x | isL x (n + 1) ∧ cnt x (n + 1) = k + 1}

/-- at least `k` ladder epochs -/
def G (k : ℕ) : Set (ℕ → ℝ) := {x | ∃ n, k ≤ cnt x n}

/-- `m` is a ladder epoch (or `0`) with exactly `k` ladder epochs in `[1, m]` -/
def C (m k : ℕ) : Set (ℕ → ℝ) := {x | isL x m ∧ cnt x m = k}

/-- the walk is positive at some time -/
def G1 : Set (ℕ → ℝ) := {x | ∃ n, 0 < s x n}

/-- time shift -/
def shift (m : ℕ) (x : ℕ → ℝ) : ℕ → ℝ := fun j => x (m + j)

lemma s_shift (x : ℕ → ℝ) (m j : ℕ) : s (shift m x) j = s x (m + j) - s x m := by
  simp only [s, shift, Finset.sum_range_add]
  ring

lemma iUnion_T (k : ℕ) : (⋃ n, T n k) = G (k + 1) := by
  ext x
  simp only [Set.mem_iUnion, T, G, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, _, h2⟩; exact ⟨n + 1, h2.ge⟩
  · intro h; exact exists_hit x k h

lemma disjoint_T (k : ℕ) : Pairwise (Function.onFun Disjoint (fun n => T n k)) := by
  intro a b hab
  refine Set.disjoint_left.2 (fun x ha hb => ?_)
  simp only [T, Set.mem_setOf_eq] at ha hb
  rcases lt_or_gt_of_ne hab with h | h
  · have := cnt_lt_of_ladder x (show a + 1 < b + 1 by omega) hb.1; omega
  · have := cnt_lt_of_ladder x (show b + 1 < a + 1 by omega) ha.1; omega

lemma iUnion_C (k : ℕ) : (⋃ m, C m k) = G k := by
  ext x
  simp only [Set.mem_iUnion, C, G, Set.mem_setOf_eq]
  constructor
  · rintro ⟨m, _, h2⟩; exact ⟨m, h2.ge⟩
  · intro h
    rcases k with _ | k
    · exact ⟨0, fun m hm => absurd hm (Nat.not_lt_zero _), cnt_zero x⟩
    · obtain ⟨m, h1, h2⟩ := exists_hit x k h
      exact ⟨m + 1, h1, h2⟩

lemma disjoint_C (k : ℕ) : Pairwise (Function.onFun Disjoint (fun m => C m k)) := by
  intro a b hab
  refine Set.disjoint_left.2 (fun x ha hb => ?_)
  simp only [C, Set.mem_setOf_eq] at ha hb
  rcases lt_or_gt_of_ne hab with h | h
  · have := cnt_lt_of_ladder x h hb.1; omega
  · have := cnt_lt_of_ladder x h ha.1; omega

lemma G_succ_eq (k : ℕ) : G (k + 1) = ⋃ m, (C m k ∩ shift m ⁻¹' G1) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, G, C, G1, Set.mem_setOf_eq,
    s_shift]
  constructor
  · intro h
    have hk : x ∈ G k := by
      obtain ⟨n, hn⟩ := h; exact ⟨n, by omega⟩
    rw [← iUnion_C] at hk
    simp only [Set.mem_iUnion, C, Set.mem_setOf_eq] at hk
    obtain ⟨m, hm1, hm2⟩ := hk
    obtain ⟨n, hn⟩ := h
    obtain ⟨l, hl1, hl2, hl3⟩ := exists_ladder_between x m n (by omega)
    refine ⟨m, ⟨hm1, hm2⟩, l - m, ?_⟩
    rw [show m + (l - m) = l by omega]
    linarith [hl3 m hl1]
  · rintro ⟨m, ⟨hm1, hm2⟩, j, hj⟩
    classical
    have hex : ∃ t, m < t ∧ s x m < s x t := by
      refine ⟨m + j, ?_, by linarith⟩
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0; simp at hj
      · omega
    have hspec := Nat.find_spec hex
    have hL : isL x (Nat.find hex) := by
      intro u hu
      by_cases hum : u ≤ m
      · rcases Nat.lt_or_eq_of_le hum with h1 | h1
        · linarith [hm1 u h1, hspec.2]
        · rw [h1]; exact hspec.2
      · have hmin := Nat.find_min hex hu
        push_neg at hmin
        linarith [hmin (by omega)]
    refine ⟨Nat.find hex, ?_⟩
    have := cnt_lt_of_ladder x hspec.1 hL
    omega

lemma measurable_s (n : ℕ) : Measurable (fun x : ℕ → ℝ => s x n) :=
  Finset.measurable_sum _ (fun j _ => measurable_pi_apply j)

lemma measurableSet_isL (n : ℕ) : MeasurableSet {x : ℕ → ℝ | isL x n} := by
  have : {x : ℕ → ℝ | isL x n} = ⋂ m ∈ Finset.range n, {x | s x m < s x n} := by
    ext x; simp [isL]
  rw [this]
  exact Finset.measurableSet_biInter _ (fun m _ => measurableSet_lt (measurable_s m) (measurable_s n))

lemma measurable_cnt (n : ℕ) : Measurable (fun x : ℕ → ℝ => cnt x n) := by
  classical
  have : (fun x : ℕ → ℝ => cnt x n) =
      fun x => ∑ j ∈ Finset.Icc 1 n, if isL x j then 1 else 0 := by
    ext x; simp only [cnt, Finset.card_filter]
  rw [this]
  exact Finset.measurable_sum _ (fun j _ =>
    Measurable.ite (measurableSet_isL j) measurable_const measurable_const)

lemma measurableSet_T (n k : ℕ) : MeasurableSet (T n k) :=
  (measurableSet_isL (n + 1)).inter ((measurable_cnt (n + 1)) (measurableSet_singleton (k + 1)))

lemma measurableSet_C (m k : ℕ) : MeasurableSet (C m k) :=
  (measurableSet_isL m).inter ((measurable_cnt m) (measurableSet_singleton k))

lemma measurableSet_G1 : MeasurableSet G1 := by
  rw [show G1 = ⋃ n, {x : ℕ → ℝ | 0 < s x n} by ext x; simp [G1]]
  exact MeasurableSet.iUnion (fun n => measurableSet_lt measurable_const (measurable_s n))

lemma measurableSet_G (k : ℕ) : MeasurableSet (G k) := by
  rw [show G k = ⋃ n, (fun x => cnt x n) ⁻¹' Set.Ici k by ext x; simp [G]]
  exact MeasurableSet.iUnion (fun n => (measurable_cnt n) measurableSet_Ici)

open Classical in
/-- the cyclic weight `1/(number of ladder epochs)` at a ladder epoch `n` -/
noncomputable def fL (n : ℕ) (x : ℕ → ℝ) : ℝ≥0∞ :=
  if isL x n then ((cnt x n : ℝ≥0∞))⁻¹ else 0

lemma measurable_fL (n : ℕ) : Measurable (fL n) := by
  classical
  unfold fL
  exact Measurable.ite (measurableSet_isL n)
    ((measurable_from_nat (f := fun k : ℕ => ((k : ℝ≥0∞))⁻¹)).comp (measurable_cnt n))
    measurable_const

lemma fL_eq (n : ℕ) (x : ℕ → ℝ) :
    fL (n + 1) x = ∑' k : ℕ, (T n k).indicator (fun _ => ((k : ℝ≥0∞) + 1)⁻¹) x := by
  classical
  unfold fL
  by_cases h : isL x (n + 1)
  · have hpos : 0 < cnt x (n + 1) := Finset.card_pos.2
      ⟨n + 1, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, le_rfl⟩, h⟩⟩
    obtain ⟨c, hc⟩ : ∃ c, cnt x (n + 1) = c + 1 := ⟨cnt x (n + 1) - 1, by omega⟩
    rw [if_pos h, hc]
    have : ∀ k : ℕ, (T n k).indicator (fun _ => ((k : ℝ≥0∞) + 1)⁻¹) x =
        if k = c then ((k : ℝ≥0∞) + 1)⁻¹ else 0 := by
      intro k
      simp only [Set.indicator_apply, T, Set.mem_setOf_eq, h, true_and, hc]
      by_cases hk : k = c
      · rw [if_pos (by omega), if_pos hk]
      · rw [if_neg (by omega), if_neg hk]
    rw [tsum_congr this, tsum_ite_eq]
    push_cast; rfl
  · rw [if_neg h]
    symm
    refine ENNReal.tsum_eq_zero.2 (fun k => ?_)
    simp [Set.indicator_apply, T, h]

/-! ### Probability layer -/

lemma meas_pi_sub {Ω' : Type*} (F : MeasurableSpace Ω') (f : Ω' → ℕ → ℝ)
    (hf : ∀ j, @Measurable Ω' ℝ F _ (fun ω => f ω j)) : @Measurable Ω' (ℕ → ℝ) F _ f :=
  measurable_pi_lambda f hf

/-- iid hypotheses of Lemma (1.6) -/
structure IID {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (Y : ℕ → Ω → ℝ) :
    Prop where
  meas : ∀ j, Measurable (Y j)
  ind : ProbabilityTheory.iIndepFun Y P
  id : ∀ j, ProbabilityTheory.IdentDistrib (Y j) (Y 0) P P

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Y : ℕ → Ω → ℝ}

/-- the path -/
def X (Y : ℕ → Ω → ℝ) (ω : Ω) : ℕ → ℝ := fun j => Y j ω

lemma measurable_X (h : IID P Y) : Measurable (X Y) := measurable_pi_lambda _ h.meas

lemma ident_reindex (h : IID P Y) {g' : ℕ → ℕ} (hg : g'.Injective) :
    IdentDistrib (fun ω j => Y (g' j) ω) (X Y) P P :=
  IdentDistrib.pi (X := fun j ω => Y (g' j) ω) (Y := fun j ω => Y j ω)
    (fun j => (h.id (g' j)).trans (h.id j).symm) (h.ind.precomp hg) h.ind

lemma markov (h : IID P Y) (m : ℕ) {E B : Set (ℕ → ℝ)} (hE : MeasurableSet E)
    (hEdep : ∀ x y : ℕ → ℝ, (∀ j < m, x j = y j) → (x ∈ E ↔ y ∈ E)) (hB : MeasurableSet B) :
    P ({ω | X Y ω ∈ E} ∩ {ω | shift m (X Y ω) ∈ B}) =
      P {ω | X Y ω ∈ E} * P {ω | X Y ω ∈ B} := by
  set mm : ℕ → MeasurableSpace Ω := fun j => MeasurableSpace.comap (Y j) inferInstance with hmm
  have h_le : ∀ j, mm j ≤ ‹MeasurableSpace Ω› := fun j => (h.meas j).comap_le
  have hI : Indep (⨆ j ∈ {j | j < m}, mm j) (⨆ j ∈ {j | m ≤ j}, mm j) P :=
    indep_iSup_of_disjoint h_le h.ind
      (Set.disjoint_left.2 (fun j h1 h2 => by simp only [Set.mem_setOf_eq] at h1 h2; omega))
  have hYm : ∀ j, Measurable[mm j] (Y j) := fun j => comap_measurable (Y j)
  let Φ : Ω → ℕ → ℝ := fun ω j => if j < m then Y j ω else 0
  have hΦ : Measurable[⨆ j ∈ {j | j < m}, mm j] Φ := by
    refine meas_pi_sub _ Φ (fun j => ?_)
    by_cases hj : j < m
    · simp only [Φ, hj, if_true]
      exact (hYm j).mono (le_iSup₂ (f := fun j _ => mm j) j hj) le_rfl
    · simp only [Φ, hj, if_false]
      exact measurable_const
  have hset1 : {ω | X Y ω ∈ E} = Φ ⁻¹' E := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    exact hEdep _ _ (fun j hj => by simp [Φ, hj, X])
  have hΨ : Measurable[⨆ j ∈ {j | m ≤ j}, mm j] (fun ω => shift m (X Y ω)) :=
    meas_pi_sub _ _ (fun j => (hYm (m + j)).mono
      (le_iSup₂ (f := fun j _ => mm j) (m + j) (by simp)) le_rfl)
  have h1 : MeasurableSet[⨆ j ∈ {j | j < m}, mm j] {ω | X Y ω ∈ E} := by
    rw [hset1]; exact hΦ hE
  rw [show {ω | shift m (X Y ω) ∈ B} = (fun ω => shift m (X Y ω)) ⁻¹' B from rfl,
    (Indep_iff _ _ _).1 hI _ _ h1 (hΨ hB)]
  congr 1
  exact (ident_reindex h (g' := fun j => m + j) (fun a b hab => by simpa using hab)).measure_mem_eq hB

/-- `p = P(some S_n > 0)` -/
noncomputable def pp (P : Measure Ω) (Y : ℕ → Ω → ℝ) : ℝ≥0∞ := P {ω | X Y ω ∈ G1}

lemma prob_G (h : IID P Y) (k : ℕ) : P {ω | X Y ω ∈ G k} = pp P Y ^ k := by
  induction k with
  | zero =>
    have : {ω | X Y ω ∈ G 0} = Set.univ := by
      ext ω; simp only [G, Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact ⟨0, Nat.zero_le _⟩
    rw [this, measure_univ, pow_zero]
  | succ k ih =>
    have hset : {ω | X Y ω ∈ G (k + 1)} =
        ⋃ m, ({ω | X Y ω ∈ C m k} ∩ {ω | shift m (X Y ω) ∈ G1}) := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, G_succ_eq,
        Set.mem_preimage]
    have hsetk : {ω | X Y ω ∈ G k} = ⋃ m, {ω | X Y ω ∈ C m k} := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion, ← iUnion_C]
    have hmeasC : ∀ m, MeasurableSet {ω | X Y ω ∈ C m k} :=
      fun m => (measurable_X h) (measurableSet_C m k)
    have hdisjC : Pairwise (Function.onFun Disjoint (fun m => {ω | X Y ω ∈ C m k})) :=
      fun a b hab => (disjoint_C k hab).preimage (X Y)
    rw [hset, measure_iUnion, pow_succ, ← ih, hsetk, measure_iUnion hdisjC hmeasC,
      ← ENNReal.tsum_mul_right]
    · refine tsum_congr (fun m => ?_)
      refine markov h m (measurableSet_C m k) (fun x y hxy => ?_) measurableSet_G1
      simp only [C, Set.mem_setOf_eq]
      rw [isL_congr hxy le_rfl, cnt_congr hxy le_rfl]
    · intro a b hab
      exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left (hdisjC hab)
    · intro m
      exact (hmeasC m).inter ((measurable_shift_X h m) measurableSet_G1)
  where
    measurable_shift_X (h : IID P Y) (m : ℕ) : Measurable (fun ω => shift m (X Y ω)) :=
      measurable_pi_lambda _ (fun j => h.meas (m + j))

lemma measurable_rot (h : IID P Y) (n i : ℕ) : Measurable (fun ω => rot (X Y ω) n i) :=
  measurable_pi_lambda _ (fun j => h.meas _)

lemma P1b (h : IID P Y) (n : ℕ) (hn : 0 < n) :
    (n : ℝ≥0∞) * ∫⁻ ω, fL n (X Y ω) ∂P = P {ω | 0 < s (X Y ω) n} := by
  have hrot : ∀ i ∈ Finset.range n,
      ∫⁻ ω, fL n (rot (X Y ω) n i) ∂P = ∫⁻ ω, fL n (X Y ω) ∂P := fun i _ =>
    ((ident_reindex h (g_injective n i)).comp (measurable_fL n)).lintegral_eq
  have hmeasS : MeasurableSet {ω | 0 < s (X Y ω) n} :=
    measurableSet_lt measurable_const ((measurable_s n).comp (measurable_X h))
  calc (n : ℝ≥0∞) * ∫⁻ ω, fL n (X Y ω) ∂P
      = ∑ i ∈ Finset.range n, ∫⁻ ω, fL n (X Y ω) ∂P := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ∑ i ∈ Finset.range n, ∫⁻ ω, fL n (rot (X Y ω) n i) ∂P :=
        (Finset.sum_congr rfl hrot).symm
    _ = ∫⁻ ω, ∑ i ∈ Finset.range n, fL n (rot (X Y ω) n i) ∂P :=
        (lintegral_finset_sum _ (fun i _ => (measurable_fL n).comp (measurable_rot h n i))).symm
    _ = ∫⁻ ω, {ω | 0 < s (X Y ω) n}.indicator 1 ω ∂P := by
        refine lintegral_congr (fun ω => ?_)
        have := cyclic (X Y ω) n hn
        simp only [fL] at this ⊢
        rw [this, Set.indicator_apply]
        simp only [Set.mem_setOf_eq, Pi.one_apply]
        try (split_ifs <;> rfl)
    _ = P {ω | 0 < s (X Y ω) n} := lintegral_indicator_one hmeasS

theorem series_eq (h : IID P Y) :
    ∑' n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | 0 < s (X Y ω) (n + 1)} =
      ∑' k : ℕ, ((k : ℝ≥0∞) + 1)⁻¹ * pp P Y ^ (k + 1) := by
  have hT : ∀ n k, MeasurableSet {ω | X Y ω ∈ T n k} :=
    fun n k => (measurable_X h) (measurableSet_T n k)
  have step1 : ∀ n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | 0 < s (X Y ω) (n + 1)} =
      ∑' k : ℕ, ((k : ℝ≥0∞) + 1)⁻¹ * P {ω | X Y ω ∈ T n k} := by
    intro n
    rw [← P1b h (n + 1) (by omega)]
    have h0 : ((n + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    have h1 : ((n + 1 : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
    rw [show ((n : ℝ≥0∞) + 1) = ((n + 1 : ℕ) : ℝ≥0∞) by push_cast; rfl,
      ← mul_assoc, ENNReal.inv_mul_cancel h0 h1, one_mul]
    rw [show (fun ω => fL (n + 1) (X Y ω)) =
        fun ω => ∑' k : ℕ, {ω | X Y ω ∈ T n k}.indicator (fun _ => ((k : ℝ≥0∞) + 1)⁻¹) ω by
      ext ω; rw [fL_eq]; rfl]
    rw [lintegral_tsum (fun k => (measurable_const.indicator (hT n k)).aemeasurable)]
    exact tsum_congr (fun k => lintegral_indicator_const (hT n k) _)
  rw [tsum_congr step1, ENNReal.tsum_comm]
  refine tsum_congr (fun k => ?_)
  rw [ENNReal.tsum_mul_left, ← measure_iUnion (f := fun n => {ω | X Y ω ∈ T n k}) (fun a b hab => (disjoint_T k hab).preimage (X Y))
    (fun n => hT n k)]
  congr 1
  rw [← prob_G h (k + 1)]
  congr 1
  ext ω
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  rw [← iUnion_T, Set.mem_iUnion]


/-! ### From the series to the ladder count -/

open Filter Topology

lemma harmonic_top : ∑' k : ℕ, ((k : ℝ≥0∞) + 1)⁻¹ = ∞ := by
  by_contra hne
  have hs := ENNReal.summable_toReal hne
  have hs' : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
    refine hs.congr (fun k => ?_)
    rw [show ((k : ℝ≥0∞) + 1) = ((k + 1 : ℕ) : ℝ≥0∞) by push_cast; rfl, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, one_div]
  exact Real.not_summable_one_div_natCast
    ((summable_nat_add_iff (f := fun m : ℕ => 1 / (m : ℝ)) 1).1 hs')

lemma series_ne_top_iff (p : ℝ≥0∞) (hp : p ≤ 1) :
    ∑' k : ℕ, ((k : ℝ≥0∞) + 1)⁻¹ * p ^ (k + 1) ≠ ∞ ↔ p < 1 := by
  constructor
  · intro h
    by_contra hlt
    have hp1 : p = 1 := le_antisymm hp (not_lt.1 hlt)
    apply h
    simp only [hp1, one_pow, mul_one]
    exact harmonic_top
  · intro h
    refine ne_top_of_le_ne_top (ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 h).ne') ?_
    rw [← ENNReal.tsum_geometric]
    refine ENNReal.tsum_le_tsum (fun k => ?_)
    rw [pow_succ]
    calc ((k : ℝ≥0∞) + 1)⁻¹ * (p ^ k * p) ≤ 1 * (p ^ k * 1) :=
          mul_le_mul' (ENNReal.inv_le_one.2 le_add_self) (mul_le_mul' le_rfl hp)
      _ = p ^ k := by rw [one_mul, mul_one]

lemma ladder_pos (x : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (h : isL x n) : 0 < s x n := by
  have := h 0 hn
  simpa [s] using this

lemma inf_ladders_freq (x : ℕ → ℝ) (hx : ∀ k, x ∈ G k) : ∃ᶠ n in atTop, 0 < s x n := by
  refine frequently_atTop.2 (fun N => ?_)
  obtain ⟨n, hn⟩ := hx (cnt x N + 1)
  obtain ⟨l, hl1, _, hl3⟩ := exists_ladder_between x N n (by omega)
  exact ⟨l, hl1.le, ladder_pos x (by omega) hl3⟩

lemma fin_ladders_bdd (x : ℕ → ℝ) (hx : ∃ k, x ∉ G k) : ∃ B, ∀ n, s x n ≤ B := by
  classical
  obtain ⟨k, hk⟩ := hx
  have hbd : ∃ c, ∀ n, cnt x n ≤ c := ⟨k, fun n => by
    by_contra hc; exact hk ⟨n, by omega⟩⟩
  have hc := Nat.find_spec hbd
  obtain ⟨n0, hn0⟩ : ∃ n0, cnt x n0 = Nat.find hbd := by
    rcases hcz : Nat.find hbd with _ | c'
    · exact ⟨0, cnt_zero x⟩
    · have hmin := Nat.find_min hbd (show c' < Nat.find hbd by omega)
      push_neg at hmin
      obtain ⟨n0, hn0⟩ := hmin
      exact ⟨n0, by have := hc n0; omega⟩
  have hconst : ∀ n, n0 ≤ n → cnt x n = cnt x n0 := fun n hn => by
    have := cnt_mono x hn; have := hc n; omega
  refine ⟨(Finset.range (n0 + 1)).sup' ⟨0, by simp⟩ (s x), ?_⟩
  set B := (Finset.range (n0 + 1)).sup' ⟨0, by simp⟩ (s x) with hB
  have hle : ∀ l ≤ n0, s x l ≤ B := fun l hl =>
    Finset.le_sup' (s x) (Finset.mem_range.2 (by omega))
  by_contra hcon
  push_neg at hcon
  have hspec := Nat.find_spec hcon
  have hgt : n0 < Nat.find hcon := by
    by_contra hh; push_neg at hh; linarith [hle _ hh]
  have hL : isL x (Nat.find hcon) := by
    intro l hl
    by_cases hl0 : l ≤ n0
    · linarith [hle l hl0]
    · have := Nat.find_min hcon hl
      push_neg at this
      linarith
  have := cnt_lt_of_ladder x hgt hL
  rw [hconst _ hgt.le] at this
  exact lt_irrefl _ this

lemma tendsto_fin_ladders (x : ℕ → ℝ) (hx : Tendsto (s x) atTop atBot) : ∃ k, x ∉ G k := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (tendsto_atBot.1 hx (-1))
  refine ⟨cnt x N + 1, fun ⟨n, hn⟩ => ?_⟩
  obtain ⟨l, hl1, _, hl3⟩ := exists_ladder_between x N n (by omega)
  have := ladder_pos x (by omega) hl3
  linarith [hN l hl1.le]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Y : ℕ → Ω → ℝ}

lemma ae_inf_ladders (h : IID P Y) (hp : pp P Y = 1) : ∀ᵐ ω ∂P, ∀ k, X Y ω ∈ G k := by
  refine ae_all_iff.2 (fun k => ?_)
  have := prob_G h k
  rw [hp, one_pow] at this
  rw [ae_iff, ← Set.compl_setOf]
  exact (prob_compl_eq_zero_iff ((measurable_X h) (measurableSet_G k))).2 this

lemma ae_fin_ladders (h : IID P Y) (hp : pp P Y < 1) : ∀ᵐ ω ∂P, ∃ k, X Y ω ∉ G k := by
  rw [ae_iff]
  have hset : {a | ¬ ∃ k, X Y a ∉ G k} = {a | ∀ k, X Y a ∈ G k} := by
    ext a; simp
  rw [hset]
  refine nonpos_iff_eq_zero.1 (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hp)
    (fun k => (measure_mono (s := {a | ∀ k, X Y a ∈ G k}) (t := {ω | X Y ω ∈ G k})
      (fun ω (hω : ∀ k, X Y ω ∈ G k) => hω k)).trans (prob_G h k).le))

lemma ae_false_absurd (H : ∀ᵐ _ω ∂P, False) : False := by
  rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at H
  exact IsProbabilityMeasure.ne_zero P H

/-- the dichotomy hypothesis supplied by the limsup lemma -/
def Dich (P : Measure Ω) (Y : ℕ → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, (∀ M : ℝ, ∃ᶠ n in atTop, M ≤ s (X Y ω) n) ∨ Tendsto (fun n => s (X Y ω) n) atTop atBot

theorem partA (h : IID P Y) (hD : Dich P Y) :
    (pp P Y < 1 ↔ ∀ᵐ ω ∂P, Tendsto (fun n => s (X Y ω) n) atTop atBot) ∧
      (pp P Y = 1 → ∀ᵐ ω ∂P, ∀ M : ℝ, ∃ᶠ n in atTop, M ≤ s (X Y ω) n) := by
  refine ⟨⟨fun hp => ?_, fun H => ?_⟩, fun hp => ?_⟩
  · filter_upwards [ae_fin_ladders h hp, hD] with ω h1 h2
    rcases h2 with h2 | h2
    · exfalso
      obtain ⟨B, hB⟩ := fin_ladders_bdd _ h1
      obtain ⟨n, hn⟩ := (h2 (B + 1)).exists
      linarith [hB n]
    · exact h2
  · by_contra hlt
    have hp1 : pp P Y = 1 := le_antisymm prob_le_one (not_lt.1 hlt)
    refine ae_false_absurd (P := P) ?_
    filter_upwards [ae_inf_ladders h hp1, H] with ω h1 h2
    obtain ⟨k, hk⟩ := tendsto_fin_ladders _ h2
    exact hk (h1 k)
  · filter_upwards [ae_inf_ladders h hp, hD] with ω h1 h2
    rcases h2 with h2 | h2
    · exact h2
    · exfalso
      obtain ⟨n, hn1, hn2⟩ := ((inf_ladders_freq _ h1).and_eventually
        (tendsto_atBot.1 h2 0)).exists
      linarith


/-! ### P3: the limsup of a nondegenerate walk is `±∞` -/

/-- `limsup S_n` in `EReal` -/
noncomputable def Lsup (x : ℕ → ℝ) : EReal := limsup (fun n => ((s x n : ℝ) : EReal)) atTop

lemma measurable_Lsup : Measurable Lsup :=
  Measurable.limsup (fun n => (measurable_s n).coe_real_ereal)

/-- translation by a real number as an order isomorphism of `EReal` -/
noncomputable def addIso (c : ℝ) : EReal ≃o EReal where
  toFun y := (c : EReal) + y
  invFun y := ((-c : ℝ) : EReal) + y
  left_inv y := by
    show ((-c : ℝ) : EReal) + ((c : EReal) + y) = y
    rw [← add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add]
  right_inv y := by
    show (c : EReal) + (((-c : ℝ) : EReal) + y) = y
    rw [← add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, zero_add]
  map_rel_iff' {a b} := by
    show (c : EReal) + a ≤ (c : EReal) + b ↔ a ≤ b
    constructor
    · intro hab
      have := add_le_add (le_refl (((-c : ℝ) : EReal))) hab
      rwa [← add_assoc, ← add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero,
        zero_add, zero_add] at this
    · intro hab
      exact add_le_add (le_refl _) hab

lemma addIso_apply (c : ℝ) (y : EReal) : addIso c y = (c : EReal) + y := rfl

lemma s_succ_shift (x : ℕ → ℝ) (n : ℕ) : s x (n + 1) = x 0 + s (shift 1 x) n := by
  rw [s_shift]
  have : s x 1 = x 0 := by simp [s]
  rw [this, Nat.add_comm 1 n]
  ring

lemma Lsup_shift (x : ℕ → ℝ) : Lsup x = (x 0 : EReal) + Lsup (shift 1 x) := by
  have h1 : Lsup x = limsup (fun n => ((s x (n + 1) : ℝ) : EReal)) atTop :=
    (limsup_nat_add (fun n => ((s x n : ℝ) : EReal)) 1).symm
  have h2 : (fun n => ((s x (n + 1) : ℝ) : EReal)) =
      (addIso (x 0)) ∘ (fun n => ((s (shift 1 x) n : ℝ) : EReal)) := by
    ext n
    simp only [Function.comp, addIso_apply]
    rw [s_succ_shift, EReal.coe_add]
  rw [h1, h2]
  exact (OrderIso.limsup_apply (addIso (x 0))).symm

/-- the event `limsup S_n ∈ ℝ` -/
def Fset : Set (ℕ → ℝ) := {x | Lsup x ≠ ⊤ ∧ Lsup x ≠ ⊥}

lemma measurableSet_Fset : MeasurableSet Fset :=
  (measurable_Lsup (measurableSet_singleton ⊤).compl).inter
    (measurable_Lsup (measurableSet_singleton ⊥).compl)

lemma Lsup_shift_facts (x : ℕ → ℝ) :
    (x ∈ Fset ↔ shift 1 x ∈ Fset) ∧
      (x ∈ Fset → (Lsup x).toReal = x 0 + (Lsup (shift 1 x)).toReal) := by
  simp only [Fset, Set.mem_setOf_eq]
  rw [Lsup_shift x]
  generalize Lsup (shift 1 x) = y
  induction y using EReal.rec <;> simp [← EReal.coe_add]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Y : ℕ → Ω → ℝ}

lemma indep_head (h : IID P Y) : IndepFun (Y 0) (fun ω => shift 1 (X Y ω)) P := by
  rw [IndepFun_iff]
  rintro t1 t2 ⟨S, hS, rfl⟩ ⟨B, hB, rfl⟩
  have := markov h 1 (E := {x | x 0 ∈ S}) (measurable_pi_apply 0 hS)
    (fun x y hxy => by simp [hxy 0 one_pos]) hB
  rw [show P {ω | X Y ω ∈ B} = P ((fun ω => shift 1 (X Y ω)) ⁻¹' B) from
    ((ident_reindex h (g' := fun j => 1 + j) (fun a b hab => by simpa using hab)).measure_mem_eq
      hB).symm] at this
  exact this

lemma ae_zero_of_charFun_one {Z : Ω → ℝ} (hZ : Measurable Z) {δ : ℝ} (hδ : 0 < δ)
    (h1 : ∀ t : ℝ, |t| < δ → ∫ ω, Complex.exp (↑(t * Z ω) * Complex.I) ∂P = 1) :
    ∀ᵐ ω ∂P, Z ω = 0 := by
  have hcos : ∀ t : ℝ, |t| < δ → ∀ᵐ ω ∂P, Real.cos (t * Z ω) = 1 := by
    intro t ht
    have hm : Measurable (fun ω => Complex.exp (↑(t * Z ω) * Complex.I)) :=
      Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
        (measurable_const.mul hZ)).mul_const _)
    have hint : Integrable (fun ω => Complex.exp (↑(t * Z ω) * Complex.I)) P :=
      (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
        (ae_of_all _ (fun ω => by rw [Complex.norm_exp_ofReal_mul_I]))
    have hre : ∫ ω, Real.cos (t * Z ω) ∂P = 1 := by
      have := integral_re hint
      rw [h1 t ht] at this
      simp only [RCLike.re_to_complex, Complex.exp_ofReal_mul_I_re, Complex.one_re] at this
      exact this
    have hcm : Measurable (fun ω => Real.cos (t * Z ω)) :=
      Real.measurable_cos.comp (measurable_const.mul hZ)
    have hcint : Integrable (fun ω => Real.cos (t * Z ω)) P :=
      (integrable_const (1 : ℝ)).mono' hcm.aestronglyMeasurable
        (ae_of_all _ (fun ω => by simpa using Real.abs_cos_le_one (t * Z ω)))
    have h0 : ∫ ω, (1 - Real.cos (t * Z ω)) ∂P = 0 := by
      rw [integral_sub (integrable_const _) hcint, hre]
      simp
    have := (integral_eq_zero_iff_of_nonneg
      (f := fun ω => 1 - Real.cos (t * Z ω))
      (fun ω => by simp only [Pi.zero_apply]; linarith [Real.cos_le_one (t * Z ω)])
      ((integrable_const _).sub hcint)).1 h0
    filter_upwards [this] with ω hω
    simp only [Pi.zero_apply] at hω
    linarith
  have ht2 : |δ / 4| < δ := by rw [abs_of_pos (by positivity)]; linarith
  have hs2 : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have ht1 : |Real.sqrt 2 * (δ / 4)| < δ := by
    rw [abs_of_pos (by positivity)]; nlinarith
  filter_upwards [hcos _ ht1, hcos _ ht2] with ω h1 h2
  obtain ⟨a, ha⟩ := (Real.cos_eq_one_iff _).1 h1
  obtain ⟨b, hb⟩ := (Real.cos_eq_one_iff _).1 h2
  by_contra hz
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hb0 : (b : ℝ) ≠ 0 := by
    intro hb0
    rw [hb0, zero_mul] at hb
    rcases mul_eq_zero.1 hb.symm with h' | h'
    · linarith
    · exact hz h'
  have hab : (a : ℝ) = Real.sqrt 2 * b := by
    refine mul_right_cancel₀ hpi ?_
    rw [ha, show Real.sqrt 2 * (b : ℝ) * (2 * Real.pi) = Real.sqrt 2 * ((b : ℝ) * (2 * Real.pi))
      by ring, hb]
    ring
  have hsq : Real.sqrt 2 = (a : ℝ) / b := (eq_div_iff hb0).2 hab.symm
  exact irrational_sqrt_two ⟨(a : ℚ) / b, by push_cast; exact hsq.symm⟩

theorem dich (h : IID P Y) (hnd : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, Y 0 ω = c) : Dich P Y := by
  have hF := measurableSet_Fset
  suffices hzero : P {ω | X Y ω ∈ Fset} = 0 by
    have := (measure_eq_zero_iff_ae_notMem).1 hzero
    filter_upwards [this] with ω hω
    simp only [Fset, Set.mem_setOf_eq, not_and_or, not_not] at hω
    rcases hω with hω | hω
    · left
      intro M
      have hlt : (M : EReal) < limsup (fun n => ((s (X Y ω) n : ℝ) : EReal)) atTop := by
        rw [show limsup (fun n => ((s (X Y ω) n : ℝ) : EReal)) atTop = Lsup (X Y ω) from rfl, hω]
        exact EReal.coe_lt_top M
      exact (frequently_lt_of_lt_limsup (by isBoundedDefault) hlt).mono
        (fun n hn => (EReal.coe_lt_coe_iff.1 hn).le)
    · right
      refine tendsto_atBot.2 (fun M => ?_)
      have hlt : limsup (fun n => ((s (X Y ω) n : ℝ) : EReal)) atTop < (M : EReal) := by
        rw [show limsup (fun n => ((s (X Y ω) n : ℝ) : EReal)) atTop = Lsup (X Y ω) from rfl, hω]
        exact EReal.bot_lt_coe M
      exact (eventually_lt_of_limsup_lt hlt).mono (fun n hn => (EReal.coe_lt_coe_iff.1 hn).le)
  by_contra hc
  classical
  let χ : ℝ → (ℕ → ℝ) → ℂ := fun t =>
    Fset.indicator (fun x => Complex.exp (↑(t * (Lsup x).toReal) * Complex.I))
  have hχm : ∀ t, Measurable (χ t) := fun t =>
    Measurable.indicator (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (measurable_const.mul measurable_Lsup.ereal_toReal)).mul_const _)) hF
  have hχb : ∀ t x, ‖χ t x‖ ≤ 1 := by
    intro t x
    simp only [χ, Set.indicator_apply]
    split_ifs
    · rw [Complex.norm_exp_ofReal_mul_I]
    · simp
  let ψ : ℝ → ℂ := fun t => ∫ ω, χ t (X Y ω) ∂P
  let φ : ℝ → ℂ := fun t => ∫ ω, Complex.exp (↑(t * Y 0 ω) * Complex.I) ∂P
  have hind := indep_head h
  have hfun : ∀ t ω, χ t (X Y ω) =
      Complex.exp (↑(t * Y 0 ω) * Complex.I) * χ t (shift 1 (X Y ω)) := by
    intro t ω
    obtain ⟨hiff, hreal⟩ := Lsup_shift_facts (X Y ω)
    simp only [χ, Set.indicator_apply]
    by_cases hz : X Y ω ∈ Fset
    · rw [if_pos hz, if_pos (hiff.1 hz), hreal hz, mul_add, Complex.ofReal_add, add_mul,
        Complex.exp_add]
      rfl
    · rw [if_neg hz, if_neg (fun h' => hz (hiff.2 h')), mul_zero]
  have hψeq : ∀ t, ψ t = φ t * ψ t := by
    intro t
    have hm1 : Measurable (fun y : ℝ => Complex.exp (↑(t * y) * Complex.I)) :=
      Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
        (measurable_const.mul measurable_id)).mul_const _)
    have e1 : ψ t = ∫ ω, Complex.exp (↑(t * Y 0 ω) * Complex.I) * χ t (shift 1 (X Y ω)) ∂P :=
      integral_congr_ae (ae_of_all _ (hfun t))
    have e2 : ∫ ω, Complex.exp (↑(t * Y 0 ω) * Complex.I) * χ t (shift 1 (X Y ω)) ∂P =
        φ t * ∫ ω, χ t (shift 1 (X Y ω)) ∂P :=
      (hind.comp hm1 (hχm t)).integral_fun_mul_eq_mul_integral
        (hm1.comp (h.meas 0)).aestronglyMeasurable
        ((hχm t).comp (measurable_pi_lambda _ (fun j => h.meas (1 + j)))).aestronglyMeasurable
    have e3 : ∫ ω, χ t (shift 1 (X Y ω)) ∂P = ψ t :=
      ((ident_reindex h (g' := fun j => 1 + j) (fun a b hab => by simpa using hab)).comp
        (hχm t)).integral_eq
    rw [e2, e3] at e1
    exact e1
  have hψc : Continuous ψ := by
    refine continuous_of_dominated (bound := fun _ => 1)
      (fun t => ((hχm t).comp (measurable_X h)).aestronglyMeasurable)
      (fun t => ae_of_all _ (fun ω => hχb t (X Y ω))) (integrable_const 1)
      (ae_of_all _ (fun ω => ?_))
    simp only [χ, Set.indicator_apply]
    split_ifs
    · exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
        (continuous_id.mul continuous_const)).mul continuous_const)
    · exact continuous_const
  have hψ0 : ψ 0 ≠ 0 := by
    have e : ψ 0 = ∫ ω, {ω | X Y ω ∈ Fset}.indicator (fun _ => (1 : ℂ)) ω ∂P :=
      integral_congr_ae (ae_of_all _ (fun ω => by simp [χ, Set.indicator_apply]))
    rw [e, integral_indicator_const (s := {ω | X Y ω ∈ Fset}) _ ((measurable_X h) hF), Complex.real_smul, mul_one]
    rw [Ne, Complex.ofReal_eq_zero, measureReal_def, ENNReal.toReal_eq_zero_iff, not_or]
    exact ⟨hc, measure_ne_top _ _⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hψc.continuousAt.eventually_ne hψ0)
  have hφ1 : ∀ t : ℝ, |t| < δ → φ t = 1 := fun t ht => by
    have hne : ψ t ≠ 0 := hball (by rw [Real.dist_eq, sub_zero]; exact ht)
    have h2 : (φ t - 1) * ψ t = 0 := by rw [sub_mul, ← hψeq t, one_mul, sub_self]
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact sub_eq_zero.1 h3
    · exact absurd h3 hne
  exact hnd ⟨0, ae_zero_of_charFun_one (h.meas 0) hδ hφ1⟩


/-! ### Assembly of (i)–(ii) given the "in which case" clause of (i) -/

lemma pp_le_one : pp P Y ≤ 1 := prob_le_one

lemma iid_neg (h : IID P Y) : IID P (fun j ω => -Y j ω) where
  meas j := (h.meas j).neg
  ind := h.ind.comp (fun _ x => -x) (fun _ => measurable_neg)
  id j := (h.id j).comp measurable_neg

lemma s_neg (x : ℕ → ℝ) (n : ℕ) : s (fun j => -x j) n = - s x n := by
  simp [s, Finset.sum_neg_distrib]

theorem partA_full (h : IID P Y) (hnd : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, Y 0 ω = c) :
    (∑' n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | 0 < s (X Y ω) (n + 1)} ≠ ∞ ↔
      ∀ᵐ ω ∂P, Tendsto (fun n => s (X Y ω) n) atTop atBot) ∧
    (∑' n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | 0 < s (X Y ω) (n + 1)} = ∞ →
      ∀ᵐ ω ∂P, ∀ M : ℝ, ∃ᶠ n in atTop, M ≤ s (X Y ω) n) := by
  have hA := partA h (dich h hnd)
  rw [series_eq h]
  refine ⟨(series_ne_top_iff _ pp_le_one).trans hA.1, fun hinf => hA.2 ?_⟩
  by_contra hne
  exact ((series_ne_top_iff _ pp_le_one).2 (lt_of_le_of_ne pp_le_one hne)) hinf

theorem negA (h : IID P Y) (hnd : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, Y 0 ω = c) :
    (∑' n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | s (X Y ω) (n + 1) < 0} ≠ ∞ ↔
      ∀ᵐ ω ∂P, Tendsto (fun n => s (X Y ω) n) atTop atTop) ∧
    (∑' n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | s (X Y ω) (n + 1) < 0} = ∞ →
      ∀ᵐ ω ∂P, ∀ M : ℝ, ∃ᶠ n in atTop, s (X Y ω) n ≤ M) := by
  have hnd' : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, (fun j ω => -Y j ω) 0 ω = c := fun ⟨c, hc⟩ =>
    hnd ⟨-c, hc.mono (fun ω hω => by simp only at hω; linarith)⟩
  have hA := partA_full (iid_neg h) hnd'
  have hsn : ∀ ω n, s (X (fun j ω => -Y j ω) ω) n = - s (X Y ω) n := fun ω n => s_neg _ n
  have hset : ∀ n : ℕ, {ω | 0 < s (X (fun j ω => -Y j ω) ω) (n + 1)} =
      {ω | s (X Y ω) (n + 1) < 0} := by
    intro n; ext ω
    simp only [Set.mem_setOf_eq, hsn]
    exact neg_pos
  simp only [hset] at hA
  refine ⟨hA.1.trans (Filter.eventually_congr (ae_of_all _ (fun ω => ?_))),
    fun hinf => (hA.2 hinf).mono (fun ω hω M => (hω (-M)).mono (fun n hn => ?_))⟩
  · simp only [hsn]
    exact tendsto_neg_atBot_iff
  · rw [hsn] at hn
    linarith

lemma tsum_exp_top (u : ℕ → ℝ) (hu : ∀ M : ℝ, ∃ᶠ n in atTop, M ≤ u n) :
    ∑' n : ℕ, ENNReal.ofReal (Real.exp (u (n + 1))) = ∞ := by
  by_contra hne
  have ht := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hne
  have hev : ∀ᶠ n in atTop, ENNReal.ofReal (Real.exp (u (n + 1))) < 1 :=
    (tendsto_order.1 ht).2 1 one_pos
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  obtain ⟨n, hn1, hn2⟩ := frequently_atTop.1 (hu 0) (N + 1)
  have := hN (n - 1) (by omega)
  rw [show n - 1 + 1 = n by omega] at this
  exact absurd this (not_lt.2 (ENNReal.one_le_ofReal.2 (Real.one_le_exp hn2)))

open SolomonRWRE.Recurrence in
theorem main_given_B (h : IID P Y) (hnd : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, Y 0 ω = c)
    (hB : (∀ᵐ ω ∂P, Tendsto (fun n => s (X Y ω) n) atTop atBot) →
      ∀ᵐ ω ∂P, ∑' n : ℕ, ENNReal.ofReal (Real.exp (s (X Y ω) (n + 1))) ≠ ∞) :
    ((∑' n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | 0 < s (X Y ω) (n + 1)} ≠ ∞ ↔
        ∀ᵐ ω ∂P, Tendsto (fun n => s (X Y ω) n) atTop atBot) ∧
      ((∀ᵐ ω ∂P, Tendsto (fun n => s (X Y ω) n) atTop atBot) →
        ∀ᵐ ω ∂P, ∑' n : ℕ, ENNReal.ofReal (Real.exp (s (X Y ω) (n + 1))) ≠ ∞)) ∧
    ((∑' n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | 0 < s (X Y ω) (n + 1)} = ∞ ∧
        ∑' n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | s (X Y ω) (n + 1) < 0} = ∞ ↔
        ∀ᵐ ω ∂P, Oscillates (fun n => s (X Y ω) n)) ∧
      ((∀ᵐ ω ∂P, Oscillates (fun n => s (X Y ω) n)) →
        ∀ᵐ ω ∂P, ∑' n : ℕ, ENNReal.ofReal (Real.exp (-s (X Y ω) (n + 1))) = ∞ ∧
          ∑' n : ℕ, ENNReal.ofReal (Real.exp (s (X Y ω) (n + 1))) = ∞)) := by
  obtain ⟨hA1, hA2⟩ := partA_full h hnd
  obtain ⟨hN1, hN2⟩ := negA h hnd
  refine ⟨⟨hA1, hB⟩, ⟨⟨fun ⟨h1, h2⟩ => ?_, fun hO => ⟨?_, ?_⟩⟩, fun hO => ?_⟩⟩
  · filter_upwards [hA2 h1, hN2 h2] with ω a b
    exact ⟨b, a⟩
  · by_contra hne
    refine ae_false_absurd (P := P) ?_
    filter_upwards [hA1.1 hne, hO] with ω a b
    obtain ⟨n, hn1, hn2⟩ := ((b.2 1).and_eventually (tendsto_atBot.1 a 0)).exists
    linarith
  · by_contra hne
    refine ae_false_absurd (P := P) ?_
    filter_upwards [hN1.1 hne, hO] with ω a b
    obtain ⟨n, hn1, hn2⟩ := ((b.1 (-1)).and_eventually (tendsto_atTop.1 a 0)).exists
    linarith
  · filter_upwards [hO] with ω hω
    exact ⟨tsum_exp_top (fun n => -s (X Y ω) n) (fun M => (hω.1 (-M)).mono (fun n hn => by
      show M ≤ -s (X Y ω) n; linarith)), tsum_exp_top _ hω.2⟩


/-! ### Part (B): `S_n → -∞` a.s. implies `Σ e^{S_n} < ∞` a.s. (bounded expected visits) -/

/-- after time `m0` the walk stays below `-1` -/
def Bq (m0 : ℕ) : Set (ℕ → ℝ) := {y | ∀ j, m0 ≤ j → s y j < -1}

lemma measurableSet_Bq (m0 : ℕ) : MeasurableSet (Bq m0) := by
  simp only [Bq, Set.setOf_forall]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_lt (measurable_s j) measurable_const

lemma window_absurd (x0 : ℕ → ℝ) (m0 : ℕ) (x : ℝ) {a b : ℕ}
    (ha : s x0 a ∈ Set.Ioc x (x + 1) ∧ shift a x0 ∈ Bq m0)
    (hb : s x0 b ∈ Set.Ioc x (x + 1)) (hab : a + m0 ≤ b) : False := by
  have h1 := ha.2 (b - a) (by omega)
  rw [s_shift, show a + (b - a) = b by omega] at h1
  have h2 := ha.1.2
  have h3 := hb.1
  linarith

open Classical in
lemma window_count (x0 : ℕ → ℝ) (m0 : ℕ) (x : ℝ) :
    ∑' m : ℕ, (if s x0 m ∈ Set.Ioc x (x + 1) ∧ shift m x0 ∈ Bq m0 then (1 : ℝ≥0∞) else 0)
      ≤ 2 * (m0 : ℝ≥0∞) := by
  by_cases hex : ∃ a, s x0 a ∈ Set.Ioc x (x + 1) ∧ shift a x0 ∈ Bq m0
  · obtain ⟨a, ha⟩ := hex
    rw [tsum_eq_sum (s := Finset.Ico (a + 1 - m0) (a + m0))]
    · calc ∑ m ∈ Finset.Ico (a + 1 - m0) (a + m0),
            (if s x0 m ∈ Set.Ioc x (x + 1) ∧ shift m x0 ∈ Bq m0 then (1 : ℝ≥0∞) else 0)
          ≤ (Finset.Ico (a + 1 - m0) (a + m0)).card • (1 : ℝ≥0∞) :=
            Finset.sum_le_card_nsmul _ _ 1 (fun i _ => by split_ifs <;> simp)
        _ ≤ 2 * (m0 : ℝ≥0∞) := by
            rw [Nat.card_Ico, nsmul_eq_mul, mul_one]
            have : (a + m0) - (a + 1 - m0) ≤ 2 * m0 := by omega
            exact_mod_cast this
    · intro b hb
      rw [if_neg]
      intro hb'
      apply hb
      rw [Finset.mem_Ico]
      constructor
      · by_contra hlt
        exact window_absurd x0 m0 x hb' ha.1 (by omega)
      · by_contra hlt
        exact window_absurd x0 m0 x ha hb'.1 (by omega)
  · have : ∀ m, (if s x0 m ∈ Set.Ioc x (x + 1) ∧ shift m x0 ∈ Bq m0 then (1 : ℝ≥0∞) else 0)
        = 0 := fun m => if_neg (fun hm => hex ⟨m, hm⟩)
    rw [tsum_congr this, tsum_zero]
    exact zero_le

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Y : ℕ → Ω → ℝ}

lemma measurable_shiftX (h : IID P Y) (m : ℕ) : Measurable (fun ω => shift m (X Y ω)) :=
  measurable_pi_lambda _ (fun j => h.meas (m + j))

lemma visits_bound (h : IID P Y) (m0 : ℕ) (x : ℝ) :
    (∑' m : ℕ, P {ω | s (X Y ω) m ∈ Set.Ioc x (x + 1)}) * P {ω | X Y ω ∈ Bq m0}
      ≤ 2 * (m0 : ℝ≥0∞) := by
  classical
  set A : ℕ → Set Ω := fun m =>
    {ω | X Y ω ∈ {y : ℕ → ℝ | s y m ∈ Set.Ioc x (x + 1)}} ∩ {ω | shift m (X Y ω) ∈ Bq m0}
    with hA
  have hAm : ∀ m, MeasurableSet (A m) := fun m =>
    (((measurable_s m).comp (measurable_X h)) measurableSet_Ioc).inter
      ((measurable_shiftX h m) (measurableSet_Bq m0))
  have hPA : ∀ m, P (A m) = P {ω | s (X Y ω) m ∈ Set.Ioc x (x + 1)} * P {ω | X Y ω ∈ Bq m0} :=
    fun m => markov h m ((measurable_s m) measurableSet_Ioc)
      (fun x' y' hxy => by
        simp only [Set.mem_setOf_eq]
        rw [s_congr hxy le_rfl]) (measurableSet_Bq m0)
  rw [← ENNReal.tsum_mul_right]
  simp_rw [← hPA]
  calc ∑' m, P (A m) = ∑' m, ∫⁻ ω, (A m).indicator 1 ω ∂P := by
        congr 1; ext m; rw [lintegral_indicator_one (hAm m)]
    _ = ∫⁻ ω, ∑' m, (A m).indicator 1 ω ∂P :=
        (lintegral_tsum (fun m => (measurable_one.indicator (hAm m)).aemeasurable)).symm
    _ ≤ ∫⁻ _ω, 2 * (m0 : ℝ≥0∞) ∂P := by
        refine lintegral_mono (fun ω => ?_)
        refine le_trans (le_of_eq ?_) (window_count (X Y ω) m0 x)
        congr 1; ext m
        simp only [A, Set.indicator_apply, Set.mem_inter_iff, Set.mem_setOf_eq, Pi.one_apply]
    _ = 2 * (m0 : ℝ≥0∞) := by simp

lemma exists_q (hT : ∀ᵐ ω ∂P, Tendsto (fun n => s (X Y ω) n) atTop atBot) :
    ∃ m0 : ℕ, P {ω | X Y ω ∈ Bq m0} ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hU : P (⋃ m0 : ℕ, {ω | X Y ω ∈ Bq m0}) = 0 := measure_iUnion_null hcon
  have h1 : ∀ᵐ ω ∂P, ω ∈ ⋃ m0 : ℕ, {ω | X Y ω ∈ Bq m0} := by
    filter_upwards [hT] with ω hω
    obtain ⟨N, hN⟩ := eventually_atTop.1 (tendsto_atBot.1 hω (-2))
    exact Set.mem_iUnion.2 ⟨N, fun j hj => by
      have := hN j hj
      linarith⟩
  have h2 : ∀ᵐ ω ∂P, ω ∉ ⋃ m0 : ℕ, {ω | X Y ω ∈ Bq m0} := by
    rw [ae_iff]; simp only [not_not, Set.setOf_mem_eq]; exact hU
  refine ae_false_absurd (P := P) ?_
  filter_upwards [h1, h2] with ω a b
  exact b a

/-- `e^{-1}` -/
noncomputable def rr : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-1))

lemma rr_lt_one : rr < 1 := ENNReal.ofReal_lt_one.2
  ((Real.exp_lt_exp.2 (by norm_num : (-1 : ℝ) < 0)).trans_eq Real.exp_zero)

/-- the unit interval `(-k-1, -k]` -/
def Ik (k : ℕ) : Set ℝ := Set.Ioc (-(k : ℝ) - 1) (-(k : ℝ) - 1 + 1)

lemma exp_le_tsum (t : ℝ) (ht : t < 0) :
    ENNReal.ofReal (Real.exp t) ≤ ∑' k : ℕ, (Ik k).indicator (fun _ => rr ^ k) t := by
  set k := ⌊-t⌋₊ with hk
  have h1 : (k : ℝ) ≤ -t := Nat.floor_le (by linarith)
  have h2 : -t < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmem : t ∈ Ik k := by
    simp only [Ik, Set.mem_Ioc]
    constructor <;> linarith
  refine le_trans ?_ (ENNReal.le_tsum k)
  rw [Set.indicator_of_mem hmem, rr, ← ENNReal.ofReal_pow (Real.exp_pos _).le,
    ← Real.exp_nat_mul]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))

theorem partB (h : IID P Y) (hT : ∀ᵐ ω ∂P, Tendsto (fun n => s (X Y ω) n) atTop atBot) :
    ∀ᵐ ω ∂P, ∑' n : ℕ, ENNReal.ofReal (Real.exp (s (X Y ω) (n + 1))) ≠ ∞ := by
  classical
  obtain ⟨m0, hq⟩ := exists_q hT
  set q := P {ω | X Y ω ∈ Bq m0}
  have hEm : ∀ n k, MeasurableSet {ω | s (X Y ω) (n + 1) ∈ Ik k} := fun n k =>
    ((measurable_s (n + 1)).comp (measurable_X h)) measurableSet_Ioc
  set g : Ω → ℝ≥0∞ := fun ω => ∑' n : ℕ, ∑' k : ℕ,
    {ω | s (X Y ω) (n + 1) ∈ Ik k}.indicator (fun _ => rr ^ k) ω with hg
  have hgm : Measurable g := Measurable.ennreal_tsum fun n => Measurable.ennreal_tsum fun k =>
    measurable_const.indicator (hEm n k)
  have hV : ∀ k, (∑' n : ℕ, P {ω | s (X Y ω) (n + 1) ∈ Ik k}) * q ≤ 2 * (m0 : ℝ≥0∞) := by
    intro k
    have hc : (∑' n : ℕ, P {ω | s (X Y ω) (n + 1) ∈ Ik k}) ≤
        ∑' m : ℕ, P {ω | s (X Y ω) m ∈ Set.Ioc (-(k : ℝ) - 1) (-(k : ℝ) - 1 + 1)} :=
      ENNReal.tsum_comp_le_tsum_of_injective (fun a b hab => Nat.succ_injective hab)
        (fun m => P {ω | s (X Y ω) m ∈ Set.Ioc (-(k : ℝ) - 1) (-(k : ℝ) - 1 + 1)})
    exact le_trans (mul_le_mul_of_nonneg_right hc zero_le) (visits_bound h m0 (-(k : ℝ) - 1))
  have hint : ∫⁻ ω, g ω ∂P = ∑' k : ℕ, rr ^ k * ∑' n : ℕ, P {ω | s (X Y ω) (n + 1) ∈ Ik k} := by
    rw [hg, lintegral_tsum (fun n => (Measurable.ennreal_tsum fun k =>
      measurable_const.indicator (hEm n k)).aemeasurable)]
    simp_rw [lintegral_tsum (fun k => (measurable_const.indicator (hEm _ k)).aemeasurable)]
    simp_rw [lintegral_indicator_const (hEm _ _)]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
  have hfin : ∫⁻ ω, g ω ∂P ≠ ∞ := by
    rw [hint]
    intro htop
    have hle : (∑' k : ℕ, rr ^ k * ∑' n : ℕ, P {ω | s (X Y ω) (n + 1) ∈ Ik k}) * q
        ≤ (∑' k : ℕ, rr ^ k) * (2 * (m0 : ℝ≥0∞)) := by
      rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right]
      refine ENNReal.tsum_le_tsum (fun k => ?_)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hV k) zero_le
    rw [htop, ENNReal.top_mul hq, ENNReal.tsum_geometric] at hle
    have hne : (1 - rr)⁻¹ * (2 * (m0 : ℝ≥0∞)) ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 rr_lt_one).ne')
        (ENNReal.mul_ne_top (by simp) (ENNReal.natCast_ne_top m0))
    exact hne (top_le_iff.1 hle)
  have hae : ∀ᵐ ω ∂P, g ω < ∞ := ae_lt_top hgm hfin
  filter_upwards [hT, hae] with ω hω hgω
  obtain ⟨N, hN⟩ := eventually_atTop.1 (tendsto_atBot.1 hω (-1))
  have hpt : ∀ n : ℕ, ENNReal.ofReal (Real.exp (s (X Y ω) (n + 1))) ≤
      (if n < N then ENNReal.ofReal (Real.exp (s (X Y ω) (n + 1))) else 0) +
        ∑' k : ℕ, {ω | s (X Y ω) (n + 1) ∈ Ik k}.indicator (fun _ => rr ^ k) ω := by
    intro n
    by_cases hn : n < N
    · rw [if_pos hn]; exact le_self_add
    · rw [if_neg hn, zero_add]
      have hlt : s (X Y ω) (n + 1) < 0 := by
        have := hN (n + 1) (by omega); linarith
      refine le_trans (exp_le_tsum _ hlt) (le_of_eq (tsum_congr fun k => ?_))
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have hsum := ENNReal.tsum_le_tsum hpt
  rw [ENNReal.tsum_add] at hsum
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨?_, hgω.ne⟩) hsum
  rw [tsum_eq_sum (s := Finset.range N)]
  · exact ENNReal.sum_ne_top.2 (fun n _ => by split_ifs <;> simp)
  · intro b hb
    rw [if_neg (by simpa using hb)]

end SpitzerLib

open MeasureTheory ProbabilityTheory Filter Topology ENNReal SolomonRWRE.Recurrence in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hmeas : ∀ j, Measurable (Y j)) (hind : iIndepFun Y P)
    (hid : ∀ j, IdentDistrib (Y j) (Y 0) P P) (hnd : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, Y 0 ω = c) :
    ((∑' n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | 0 < partialSum Y (n + 1) ω} ≠ ∞ ↔
        ∀ᵐ ω ∂P, Tendsto (fun n => partialSum Y n ω) atTop atBot) ∧
      ((∀ᵐ ω ∂P, Tendsto (fun n => partialSum Y n ω) atTop atBot) →
        ∀ᵐ ω ∂P, ∑' n : ℕ, ENNReal.ofReal (Real.exp (partialSum Y (n + 1) ω)) ≠ ∞)) ∧
    ((∑' n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | 0 < partialSum Y (n + 1) ω} = ∞ ∧
        ∑' n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | partialSum Y (n + 1) ω < 0} = ∞ ↔
        ∀ᵐ ω ∂P, Oscillates (fun n => partialSum Y n ω)) ∧
      ((∀ᵐ ω ∂P, Oscillates (fun n => partialSum Y n ω)) →
        ∀ᵐ ω ∂P, ∑' n : ℕ, ENNReal.ofReal (Real.exp (-partialSum Y (n + 1) ω)) = ∞ ∧
          ∑' n : ℕ, ENNReal.ofReal (Real.exp (partialSum Y (n + 1) ω)) = ∞)) := by
  exact SpitzerLib.main_given_B (P := P) ⟨hmeas, hind, hid⟩ hnd (SpitzerLib.partB ⟨hmeas, hind, hid⟩)
