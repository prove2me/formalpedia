-- Prove2me | solution 1 for RealPinwheel.FiveSixths.dominance_interval
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:48:32.993343+00:00
-- url     : https://prove2.me/submissions/09b7ac2d-8104-45cd-9fbf-a7dd93e7b1dc

import Definitions.Def_RealPinwheel_FiveSixths_Word
open RealPinwheel.FiveSixths

private lemma windowCount_count {n : ℕ} (S : ℕ → Fin n) (i : Fin n) (m h : ℕ) :
    windowCount S i m h = Nat.count (fun t => S (m + t) = i) h := by
  rw [Nat.count_eq_card_filter_range]
  rfl

private lemma prefix_window {n : ℕ} (S : ℕ → Fin n) (i : Fin n) (m h : ℕ) :
    Nat.count (fun t => S t = i) (m + h) =
      Nat.count (fun t => S t = i) m + windowCount S i m h := by
  rw [Nat.count_add, windowCount_count]

private lemma periodic_prefix {n : ℕ} (S : ℕ → Fin n) (L : ℕ)
    (hper : ∀ t, S (t + L) = S t) (j : Fin n) (t : ℕ) :
    Nat.count (fun t => S t = j) (t + L) =
      Nat.count (fun t => S t = j) t + Nat.count (fun t => S t = j) L := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show t + 1 + L = (t + L) + 1 by omega]
    rw [Nat.count_succ, Nat.count_succ, ih, hper]
    omega

private lemma periodic_prefix_mul {n : ℕ} (S : ℕ → Fin n) (L : ℕ)
    (hper : ∀ t, S (t + L) = S t) (j : Fin n) (t q : ℕ) :
    Nat.count (fun t => S t = j) (t + q * L) =
      Nat.count (fun t => S t = j) t + q * Nat.count (fun t => S t = j) L := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, periodic_prefix S L hper j, ih]
    ring

private lemma periodic_mul {n : ℕ} (S : ℕ → Fin n) (L : ℕ)
    (hper : ∀ t, S (t + L) = S t) (t q : ℕ) : S (t + q * L) = S t := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, hper, ih]

private lemma windowCount_decompose {n : ℕ} (S : ℕ → Fin n) (L : ℕ)
    (hper : ∀ t, S (t + L) = S t) (i : Fin n) (m q r : ℕ) :
    windowCount S i m (q * L + r) =
      q * windowCount S i 0 L + windowCount S i m r := by
  have h := periodic_prefix_mul S L hper i (m + r) q
  have h1 := prefix_window S i m (q * L + r)
  have h2 := prefix_window S i m r
  have h3 := prefix_window S i 0 L
  rw [show m + r + q * L = m + (q * L + r) by omega] at h
  simp only [Nat.zero_add, Nat.count_zero, Nat.zero_add] at h3
  rw [h3] at h
  omega

private lemma windowCount_start_mod {n : ℕ} (S : ℕ → Fin n) (L : ℕ)
    (hper : ∀ t, S (t + L) = S t) (i : Fin n) (m h : ℕ) :
    windowCount S i m h = windowCount S i (m % L) h := by
  unfold windowCount
  congr 1
  ext t
  have he : m + t = (m % L + t) + (m / L) * L := by
    have := Nat.mod_add_div m L
    nlinarith
  simp only [Finset.mem_filter]
  rw [he, periodic_mul S L hper]

private lemma windowCount_mono {n : ℕ} (S : ℕ → Fin n) (i : Fin n) (m : ℕ)
    {r s : ℕ} (h : r ≤ s) : windowCount S i m r ≤ windowCount S i m s := by
  apply Finset.card_mono
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
  exact ⟨lt_of_lt_of_le ht.1 h, ht.2⟩

private lemma word_periodic {n : ℕ} (w : Word n) (t : ℕ) :
    wordSchedule w (t + w.length) = wordSchedule w t := by
  unfold wordSchedule
  congr 1
  apply Fin.ext
  simp

private lemma word_count_zero {n : ℕ} (w : Word n) (i : Fin n) :
    windowCount (wordSchedule w) i 0 w.length = occurrences w i := by
  classical
  unfold windowCount occurrences
  apply Finset.card_bij (fun t ht => (⟨t, (Finset.mem_range.mp (Finset.mem_filter.mp ht).1)⟩ : Fin w.length))
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [wordSchedule, Nat.mod_eq_of_lt ht.1] using ht.2
  · intro a ha b hb he
    exact congrArg Fin.val he
  · intro t ht
    refine ⟨t.val, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨t.isLt, by simpa [wordSchedule, Nat.mod_eq_of_lt t.isLt] using ht⟩
    · exact Fin.ext rfl

private lemma word_count_pos {n : ℕ} (w : Word n) (i : Fin n) : 0 < occurrences w i := by
  obtain ⟨t, ht⟩ := w.covers i
  apply Finset.card_pos.mpr
  exact ⟨t, by simp [ht]⟩

private lemma windowCount_zero {n : ℕ} (S : ℕ → Fin n) (i : Fin n) (m : ℕ) :
    windowCount S i m 0 = 0 := by simp [windowCount]

private lemma word_count_period {n : ℕ} (w : Word n) (i : Fin n) (m : ℕ) :
    windowCount (wordSchedule w) i m w.length = occurrences w i := by
  have h := windowCount_decompose (wordSchedule w) w.length (word_periodic w) i m 1 0
  simpa [word_count_zero, windowCount_zero] using h

private lemma admissible_mean {n : ℕ} (w : Word n) (i : Fin n) (d : ℝ)
    (hd : d ∈ admissibleDensities w i) : d * (w.length : ℝ) ≤ occurrences w i := by
  have hp := hd.1
  by_contra h
  have heps : 0 < d * (w.length : ℝ) - occurrences w i := by linarith
  obtain ⟨q, hq⟩ := exists_nat_ge (1 / (d * (w.length : ℝ) - occurrences w i))
  have hq' : 1 ≤ (q : ℝ) * (d * (w.length : ℝ) - occurrences w i) := (div_le_iff₀ heps).mp hq
  let ell := q * occurrences w i + 1
  have hell : 0 < ell := by dsimp [ell]; omega
  have hR : (ell : ℝ) ≤ ((q * w.length : ℕ) : ℝ) * d := by
    dsimp [ell]
    push_cast
    nlinarith
  have hceil : ⌈(ell : ℝ) * (1 / d)⌉₊ ≤ q * w.length := by
    apply Nat.ceil_le.mpr
    simpa only [div_eq_mul_inv, one_mul] using (div_le_iff₀ hp).mpr hR
  have hc := (hd.2 ell hell 0).trans (windowCount_mono (wordSchedule w) i 0 hceil)
  have he := windowCount_decompose (wordSchedule w) w.length (word_periodic w) i 0 q 0
  simp only [Nat.add_zero, windowCount_zero, word_count_zero] at he
  rw [he] at hc
  dsimp [ell] at hc
  omega

private lemma admissible_residual {n : ℕ} (w : Word n) (i : Fin n) (d : ℝ)
    (hd : d ∈ admissibleDensities w i) (m r : ℕ) :
    (r : ℝ) < ((windowCount (wordSchedule w) i m r + 1 : ℕ) : ℝ) * (1 / d) := by
  by_contra h
  let ell := windowCount (wordSchedule w) i m r + 1
  have hell : 0 < ell := by dsimp [ell]; omega
  have hc : ⌈(ell : ℝ) * (1 / d)⌉₊ ≤ r := Nat.ceil_le.mpr (not_lt.mp h)
  have := (hd.2 ell hell m).trans (windowCount_mono (wordSchedule w) i m hc)
  dsimp [ell] at this
  omega

private lemma distance_nonempty {n : ℕ} (w : Word n) (i : Fin n) (t k : ℕ) :
    {d : ℕ | k ≤ windowCount (wordSchedule w) i (t + 1) d}.Nonempty := by
  refine ⟨k * w.length, ?_⟩
  change k ≤ windowCount (wordSchedule w) i (t + 1) (k * w.length)
  have he := windowCount_decompose (wordSchedule w) w.length (word_periodic w) i (t + 1) k 0
  simp only [Nat.add_zero, word_count_zero, windowCount_zero] at he
  rw [he]
  exact (Nat.le_mul_of_pos_right k (word_count_pos w i))

private lemma distance_spec {n : ℕ} (w : Word n) (i : Fin n) (t k : ℕ) :
    k ≤ windowCount (wordSchedule w) i (t + 1) (occurrenceDistance w i t k) :=
  csInf_mem (distance_nonempty w i t k)

private lemma distance_le {n : ℕ} (w : Word n) (i : Fin n) (t k r : ℕ)
    (h : k ≤ windowCount (wordSchedule w) i (t + 1) r) :
    occurrenceDistance w i t k ≤ r :=
  csInf_le (OrderBot.bddBelow _) h

private lemma distance_gt {n : ℕ} (w : Word n) (i : Fin n) (t k r : ℕ)
    (h : windowCount (wordSchedule w) i (t + 1) r < k) : r < occurrenceDistance w i t k := by
  by_contra he
  have := (distance_spec w i t k).trans (windowCount_mono (wordSchedule w) i (t + 1) (not_lt.mp he))
  omega

private lemma distance_start_mod {n : ℕ} (w : Word n) (i : Fin n) (t k : ℕ) :
    occurrenceDistance w i t k = occurrenceDistance w i (t % w.length) k := by
  unfold occurrenceDistance
  congr 1
  ext h
  change (k ≤ windowCount (wordSchedule w) i (t + 1) h) ↔
    (k ≤ windowCount (wordSchedule w) i (t % w.length + 1) h)
  rw [windowCount_start_mod (wordSchedule w) w.length (word_periodic w) i (t + 1) h,
    windowCount_start_mod (wordSchedule w) w.length (word_periodic w) i (t % w.length + 1) h]
  simp [Nat.add_mod]

private lemma distance_le_gap {n : ℕ} (w : Word n) (i : Fin n) (t k : ℕ)
    (ht : wordSchedule w t = i) : occurrenceDistance w i t k ≤ cyclicGap w i k := by
  classical
  rw [distance_start_mod]
  let u : Fin w.length := ⟨t % w.length, Nat.mod_lt _ w.positive_length⟩
  have hu : w.letter u = i := ht
  have h := Finset.le_sup (s := Finset.univ) (f := fun s : Fin w.length =>
    if w.letter s = i then occurrenceDistance w i s.val k else 0) (Finset.mem_univ u)
  simpa [u, cyclicGap, hu] using h

private lemma admissible_gaps {n : ℕ} (w : Word n) (i : Fin n) (d : ℝ)
    (hd : d ∈ admissibleDensities w i) (k : ℕ) (hk : 0 < k)
    (hG : 1 < cyclicGap w i k) :
    d * ((cyclicGap w i k : ℝ) - 1) < (k : ℝ) := by
  classical
  have hne : (Finset.univ : Finset (Fin w.length)).Nonempty :=
    ⟨⟨0, w.positive_length⟩, Finset.mem_univ _⟩
  obtain ⟨t, ht, he⟩ := Finset.exists_mem_eq_sup Finset.univ hne
    (fun s : Fin w.length => if w.letter s = i then occurrenceDistance w i s.val k else 0)
  change cyclicGap w i k = _ at he
  have hti : w.letter t = i := by
    by_contra h
    simp only [h, ↓reduceIte] at he
    omega
  simp only [hti, ↓reduceIte] at he
  let g := occurrenceDistance w i t.val k
  have hg : 1 < g := by simpa [g, he] using hG
  have hc : windowCount (wordSchedule w) i (t.val + 1) (g - 1) < k := by
    by_contra h
    have hh := distance_le w i t.val k (g - 1) (not_lt.mp h)
    change g ≤ g - 1 at hh
    omega
  have hw := admissible_residual w i d hd (t.val + 1) (g - 1)
  have hcr : ((windowCount (wordSchedule w) i (t.val + 1) (g - 1) + 1 : ℕ) : ℝ) ≤ k := by
    exact_mod_cast (show windowCount (wordSchedule w) i (t.val + 1) (g - 1) + 1 ≤ k by omega)
  have hr : ((g - 1 : ℕ) : ℝ) < (k : ℝ) / d := by
    calc
      _ < _ := hw
      _ ≤ _ := by simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_right hcr (le_of_lt (one_div_pos.mpr hd.1))
  have he' : ((g - 1 : ℕ) : ℝ) = (g : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ g), Nat.cast_one]
  rw [he'] at hr
  have hh := (lt_div_iff₀ hd.1).mp hr
  rw [he]
  change d * ((g : ℝ) - 1) < k
  nlinarith

private lemma windowCount_add {n : ℕ} (S : ℕ → Fin n) (i : Fin n) (m a b : ℕ) :
    windowCount S i m (a + b) = windowCount S i m a + windowCount S i (m + a) b := by
  simp only [windowCount_count, Nat.count_add]
  simp only [Nat.add_assoc]

private lemma word_count_shift {n : ℕ} (w : Word n) (i : Fin n) (m r : ℕ) :
    windowCount (wordSchedule w) i (m + w.length) r = windowCount (wordSchedule w) i m r := by
  unfold windowCount
  congr 1
  ext t
  simp only [Finset.mem_filter]
  rw [show m + w.length + t = (m + t) + w.length by omega, word_periodic]

private lemma preceding_occurrence {n : ℕ} (w : Word n) (i : Fin n) (m : ℕ) :
    ∃ t < m + w.length, wordSchedule w t = i ∧
      ∀ u, t < u → u < m + w.length → wordSchedule w u ≠ i := by
  classical
  let T := (Finset.range (m + w.length)).filter fun t => wordSchedule w t = i
  have hne : T.Nonempty := by
    obtain ⟨s, hs⟩ := w.covers i
    refine ⟨s.val, ?_⟩
    simp only [T, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by simpa [wordSchedule, Nat.mod_eq_of_lt s.isLt] using hs⟩
  let t := T.max' hne
  have ht := Finset.max'_mem T hne
  change t ∈ T at ht
  simp only [T, Finset.mem_filter, Finset.mem_range] at ht
  refine ⟨t, ht.1, ht.2, ?_⟩
  intro u htu hum hu
  have hm : u ∈ T := by simp [T, Finset.mem_filter, hum, hu]
  have := Finset.le_max' T u hm
  change u ≤ t at this
  omega

private lemma residual_gap_bound {n : ℕ} (w : Word n) (i : Fin n) (m r : ℕ) :
    r < cyclicGap w i (windowCount (wordSchedule w) i m r + 1) := by
  classical
  obtain ⟨t, htm, hti, hmax⟩ := preceding_occurrence w i m
  let a := m + w.length - (t + 1)
  have he : t + 1 + a = m + w.length := by dsimp [a]; omega
  have hzero : windowCount (wordSchedule w) i (t + 1) a = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_range] at hu
    exact hmax (t + 1 + u) (by omega) (by omega) hu.2
  have hc : windowCount (wordSchedule w) i (t + 1) (a + r) =
      windowCount (wordSchedule w) i m r := by
    rw [windowCount_add, he, hzero, Nat.zero_add, word_count_shift]
  have hg := distance_gt w i t (windowCount (wordSchedule w) i m r + 1) (a + r) (by rw [hc]; omega)
  have hg' := distance_le_gap w i t (windowCount (wordSchedule w) i m r + 1) hti
  omega

private lemma finite_task {n : ℕ} (S : ℕ → Fin n) (L : ℕ) (hL : 0 < L)
    (hper : ∀ t, S (t + L) = S t) (a : ℝ) (i : Fin n)
    (ha : 0 < a) (hmean : (L : ℝ) ≤ (windowCount S i 0 L : ℝ) * a)
    (hwin : ∀ m r : ℕ, m < L → r < L →
      (r : ℝ) < ((windowCount S i m r + 1 : ℕ) : ℝ) * a) :
    ∀ ell : ℕ, 0 < ell → ∀ m : ℕ, ell ≤ windowCount S i m ⌈(ell : ℝ) * a⌉₊ := by
  intro ell hell m
  let H := ⌈(ell : ℝ) * a⌉₊
  let q := H / L
  let r := H % L
  have hr : r < L := Nat.mod_lt _ hL
  have he : H = q * L + r := by
    dsimp [q, r]
    nlinarith [Nat.mod_add_div H L]
  have hc : windowCount S i m H = q * windowCount S i 0 L + windowCount S i m r := by
    rw [he, windowCount_decompose S L hper]
  have hw := hwin (m % L) r (Nat.mod_lt _ hL) hr
  rw [← windowCount_start_mod S L hper i m r] at hw
  have hM := hmean
  have hH : (ell : ℝ) * a ≤ (H : ℝ) := Nat.le_ceil _
  by_contra hn
  change ¬ ell ≤ windowCount S i m H at hn
  have hell' : q * windowCount S i 0 L + (windowCount S i m r + 1) ≤ ell := by omega
  have hellR : (q : ℝ) * (windowCount S i 0 L : ℝ) + (windowCount S i m r : ℝ) + 1 ≤ (ell : ℝ) := by
    exact_mod_cast hell'
  have heR : (H : ℝ) = (q : ℝ) * L + r := by exact_mod_cast he
  have hm : (q : ℝ) * L ≤ (q : ℝ) * ((windowCount S i 0 L : ℝ) * a) :=
    mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg _)
  push_cast at hw
  nlinarith [mul_le_mul_of_nonneg_right hellR (le_of_lt (ha))]

private lemma gaps_residual {n : ℕ} (w : Word n) (i : Fin n) (d : ℝ) (hd : 0 < d)
    (hm : d * (w.length : ℝ) ≤ occurrences w i)
    (hg : ∀ k ∈ Finset.Icc 1 (occurrences w i), 1 < cyclicGap w i k →
      d * ((cyclicGap w i k : ℝ) - 1) < k)
    (m r : ℕ) (hr : r < w.length) :
    (r : ℝ) < ((windowCount (wordSchedule w) i m r + 1 : ℕ) : ℝ) * (1 / d) := by
  let c := windowCount (wordSchedule w) i m r
  have hc : c ≤ occurrences w i := by
    exact (windowCount_mono (wordSchedule w) i m hr.le).trans_eq (word_count_period w i m)
  have hR : (r : ℝ) * d < (c + 1 : ℕ) := by
    by_cases he : c = occurrences w i
    · have hrR : (r : ℝ) < w.length := by exact_mod_cast hr
      have hh := mul_lt_mul_of_pos_right hrR hd
      have hcR : (occurrences w i : ℝ) < (c + 1 : ℕ) := by exact_mod_cast (show occurrences w i < c + 1 by omega)
      nlinarith
    · have hci : c + 1 ∈ Finset.Icc 1 (occurrences w i) := by simp only [Finset.mem_Icc]; omega
      have hrg : r < cyclicGap w i (c + 1) := residual_gap_bound w i m r
      by_cases hzero : r = 0
      · subst r
        have hp : (0 : ℝ) < (c + 1 : ℕ) := by exact_mod_cast (show 0 < c + 1 by omega)
        simpa using hp
      · have hG : 1 < cyclicGap w i (c + 1) := by omega
        have hh := hg (c + 1) hci hG
        have hrr : (r : ℝ) ≤ (cyclicGap w i (c + 1) : ℝ) - 1 := by
          have hn : r + 1 ≤ cyclicGap w i (c + 1) := by omega
          have hnR : (r : ℝ) + 1 ≤ cyclicGap w i (c + 1) := by exact_mod_cast hn
          linarith
        nlinarith [mul_le_mul_of_nonneg_left hrr hd.le]
  simpa only [div_eq_mul_inv, one_mul] using (lt_div_iff₀ hd).mpr hR

private lemma finite_characterization {n : ℕ} (w : Word n) (i : Fin n) (d : ℝ) (hd : 0 < d) :
    d ∈ admissibleDensities w i ↔
      d * (w.length : ℝ) ≤ occurrences w i ∧
      ∀ k ∈ Finset.Icc 1 (occurrences w i), 1 < cyclicGap w i k →
        d * ((cyclicGap w i k : ℝ) - 1) < k := by
  constructor
  · intro h
    exact ⟨admissible_mean w i d h, fun k hk hG => admissible_gaps w i d h k (by simp only [Finset.mem_Icc] at hk; omega) hG⟩
  · rintro ⟨hm, hg⟩
    refine ⟨hd, ?_⟩
    apply finite_task (wordSchedule w) w.length w.positive_length (word_periodic w) (1 / d) i (one_div_pos.mpr hd)
    · rw [word_count_zero]
      have hh : (w.length : ℝ) ≤ (occurrences w i : ℝ) / d := (le_div_iff₀ hd).mpr (by nlinarith)
      simpa only [div_eq_mul_inv, one_mul] using hh
    · intro m r hm' hr
      exact gaps_residual w i d hd hm hg m r hr

private lemma gap_den_pos {n : ℕ} (w : Word n) (i : Fin n) (k : ℕ)
    (h : 1 < cyclicGap w i k) : 0 < (cyclicGap w i k : ℝ) - 1 := by
  have hh : (1 : ℝ) < cyclicGap w i k := by exact_mod_cast h
  linarith

private lemma endpoint_positive {n : ℕ} (w : Word n) (i : Fin n) : 0 < endpoint w i := by
  classical
  unfold endpoint
  apply (Finset.lt_min'_iff _ _).mpr
  intro b hb
  simp only [endpointBounds, Finset.mem_insert, Finset.mem_image, Finset.mem_filter] at hb
  rcases hb with rfl | ⟨k, ⟨hk, hg⟩, rfl⟩
  · exact div_pos (by exact_mod_cast word_count_pos w i) (by exact_mod_cast w.positive_length)
  · exact div_pos (by have := (Finset.mem_Icc.mp hk).1; exact_mod_cast (show 0 < k by omega))
      (gap_den_pos w i k hg)

private lemma finite_ratio {n : ℕ} (w : Word n) (i : Fin n) (d : ℝ) (hd : 0 < d) :
    d ∈ admissibleDensities w i ↔
      d ≤ (occurrences w i : ℝ) / w.length ∧
      ∀ k ∈ Finset.Icc 1 (occurrences w i), 1 < cyclicGap w i k →
        d < (k : ℝ) / ((cyclicGap w i k : ℝ) - 1) := by
  rw [finite_characterization w i d hd]
  have hL : (0 : ℝ) < w.length := by exact_mod_cast w.positive_length
  constructor
  · rintro ⟨hm, hg⟩
    exact ⟨(le_div_iff₀ hL).mpr hm, fun k hk hG =>
      (lt_div_iff₀ (gap_den_pos w i k hG)).mpr (hg k hk hG)⟩
  · rintro ⟨hm, hg⟩
    exact ⟨(le_div_iff₀ hL).mp hm, fun k hk hG =>
      (lt_div_iff₀ (gap_den_pos w i k hG)).mp (hg k hk hG)⟩

private lemma endpoint_order {n : ℕ} (w : Word n) (i : Fin n) (d : ℝ) :
    (d ≤ (occurrences w i : ℝ) / w.length ∧
      ∀ k ∈ Finset.Icc 1 (occurrences w i), 1 < cyclicGap w i k →
        d < (k : ℝ) / ((cyclicGap w i k : ℝ) - 1)) ↔
      d < endpoint w i ∨ d = endpoint w i ∧ closedEndpoint w i := by
  classical
  have hmean : (occurrences w i : ℝ) / w.length ∈ endpointBounds w i := by simp [endpointBounds]
  have hgap : ∀ k ∈ Finset.Icc 1 (occurrences w i), 1 < cyclicGap w i k →
      (k : ℝ) / ((cyclicGap w i k : ℝ) - 1) ∈ endpointBounds w i := by
    intro k hk hG
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hG⟩, rfl⟩)
  have hle : ∀ b ∈ endpointBounds w i, endpoint w i ≤ b := by
    intro b hb
    exact Finset.min'_le _ _ hb
  constructor
  · rintro ⟨hm, hg⟩
    have hd : d ≤ endpoint w i := by
      apply Finset.le_min'
      intro b hb
      simp only [endpointBounds, Finset.mem_insert, Finset.mem_image, Finset.mem_filter] at hb
      rcases hb with rfl | ⟨k, ⟨hk, hG⟩, rfl⟩
      · exact hm
      · exact (hg k hk hG).le
    rcases lt_or_eq_of_le hd with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      intro k hk hG he
      have hh := hg k hk hG
      rw [he, ← h] at hh
      exact (lt_irrefl d) hh
  · intro h
    constructor
    · exact (h.elim (fun h => h.le) (fun h => h.1.le)).trans (hle _ hmean)
    · intro k hk hG
      have hu := hle _ (hgap k hk hG)
      rcases h with h | ⟨h, hc⟩
      · exact h.trans_le hu
      · rw [h]
        rcases lt_or_eq_of_le hu with hlt | he
        · exact hlt
        · exact False.elim (hc k hk hG he.symm)

theorem solution {n : ℕ} (w : Word n) (i : Fin n) :
    0 < endpoint w i ∧
    admissibleDensities w i =
      {d | 0 < d ∧ (d < endpoint w i ∨ d = endpoint w i ∧ closedEndpoint w i)} ∧
    ∀ d : ℝ, 0 < d →
      (d ∈ admissibleDensities w i ↔
        d * (w.length : ℝ) ≤ (occurrences w i : ℝ) ∧
        ∀ k ∈ Finset.Icc 1 (occurrences w i), 1 < cyclicGap w i k →
          d * ((cyclicGap w i k : ℝ) - 1) < (k : ℝ)) := by
  refine ⟨endpoint_positive w i, ?_, finite_characterization w i⟩
  ext d
  constructor
  · intro h
    exact ⟨h.1, (endpoint_order w i d).mp ((finite_ratio w i d h.1).mp h)⟩
  · rintro ⟨hd, hh⟩
    exact (finite_ratio w i d hd).mpr ((endpoint_order w i d).mpr hh)
