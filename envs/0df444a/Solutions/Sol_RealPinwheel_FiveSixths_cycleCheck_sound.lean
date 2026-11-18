-- Prove2me | solution 1 for RealPinwheel.FiveSixths.cycleCheck_sound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T03:07:39.534286+00:00
-- url     : https://prove2.me/submissions/5acffd09-8c2d-4398-ac25-0cfe73dc554a

import Definitions.Def_RealPinwheel_FiveSixths_CycleCheck
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

/-- Finite window inequalities imply every multiplicity requirement. -/
private theorem finiteWindow_valid {n : ℕ} (S : ℕ → Fin n) (L : ℕ) (hL : 0 < L)
    (hper : ∀ t, S (t + L) = S t) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i)
    (hmean : ∀ i, (L : ℝ) ≤ (windowCount S i 0 L : ℝ) * a i)
    (hwin : ∀ (i : Fin n) (m r : ℕ), m < L → r < L →
      (r : ℝ) < ((windowCount S i m r : ℕ) + 1 : ℕ) * a i) : Valid a S := by
  intro i ell hell m
  let H := ⌈(ell : ℝ) * a i⌉₊
  let q := H / L
  let r := H % L
  have hr : r < L := Nat.mod_lt _ hL
  have he : H = q * L + r := by
    dsimp [q, r]
    nlinarith [Nat.mod_add_div H L]
  have hc : windowCount S i m H = q * windowCount S i 0 L + windowCount S i m r := by
    rw [he, windowCount_decompose S L hper]
  have hw := hwin i (m % L) r (Nat.mod_lt _ hL) hr
  rw [← windowCount_start_mod S L hper i m r] at hw
  have hM := hmean i
  have hH : (ell : ℝ) * a i ≤ (H : ℝ) := Nat.le_ceil _
  by_contra hn
  change ¬ ell ≤ windowCount S i m H at hn
  have hell' : q * windowCount S i 0 L + (windowCount S i m r + 1) ≤ ell := by omega
  have hellR : (q : ℝ) * (windowCount S i 0 L : ℝ) + (windowCount S i m r : ℝ) + 1 ≤ (ell : ℝ) := by
    exact_mod_cast hell'
  have heR : (H : ℝ) = (q : ℝ) * L + r := by exact_mod_cast he
  have hm : (q : ℝ) * L ≤ (q : ℝ) * ((windowCount S i 0 L : ℝ) * a i) :=
    mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg _)
  push_cast at hw
  nlinarith [mul_le_mul_of_nonneg_right hellR (le_of_lt (ha i))]

theorem solution {n : ℕ} (w : Array (Fin n)) (num den : Fin n → ℕ)
    (strict : Fin n → Bool) (hcheck : cycleCheck w num den strict = true)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, if strict i then (den i : ℝ) / num i < a i
      else (den i : ℝ) / num i ≤ a i) :
    ∃ (L : ℕ) (S : ℕ → Fin n), L = w.size ∧ Periodic S L ∧ Valid a S := by
  have hL : 0 < w.size := by
    by_contra h
    simp [cycleCheck, h] at hcheck
  let S := cycleSchedule w hL
  have hper : ∀ t, S (t + w.size) = S t := by
    intro t
    simp [S, cycleSchedule]
  refine ⟨w.size, S, rfl, ⟨hL, hper⟩, ?_⟩
  simp only [cycleCheck, dif_pos hL, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_finRange, forall_true_left] at hcheck
  simp only [cyclePrefixes, Array.getElem_ofFn] at hcheck
  apply finiteWindow_valid S w.size hL hper a ha
  · intro i
    have hi := hcheck i
    have hn : (0 : ℝ) < num i := by exact_mod_cast hi.1.1.1
    have hb' : (den i : ℝ) / num i ≤ a i := by
      have hh := hb i
      split_ifs at hh with hs
      · exact hh.le
      · exact hh
    have hd : (den i : ℝ) ≤ (num i : ℝ) * a i := by
      have := (div_le_iff₀ hn).mp hb'
      nlinarith
    have hc : (num i : ℝ) * w.size ≤ (den i : ℝ) * windowCount S i 0 w.size := by
      have hh := hi.1.2
      have he : Nat.count (fun s => cycleSchedule w hL s = i) w.size =
          windowCount S i 0 w.size := by simp [windowCount_count, S]
      rw [he] at hh
      exact_mod_cast hh
    apply (mul_le_mul_iff_right₀ hn).mp
    calc
      _ ≤ (den i : ℝ) * windowCount S i 0 w.size := hc
      _ ≤ ((num i : ℝ) * a i) * windowCount S i 0 w.size :=
        mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg _)
      _ = _ := by ring
  · intro i m r hm hr
    have hi := hcheck i
    have hn : (0 : ℝ) < num i := by exact_mod_cast hi.1.1.1
    have hh := hi.2 ⟨m, hm⟩ ⟨r, hr⟩
    have he : Nat.count (fun s => cycleSchedule w hL s = i) (m + r) -
        Nat.count (fun s => cycleSchedule w hL s = i) m = windowCount S i m r := by
      have hh := prefix_window S i m r
      change Nat.count (fun s => S s = i) (m + r) - Nat.count (fun s => S s = i) m = _
      omega
    simp only [Fin.val_mk, he] at hh
    have hb' := hb i
    have hC : (0 : ℝ) < (windowCount S i m r + 1 : ℕ) := by positivity
    apply (mul_lt_mul_iff_right₀ hn).mp
    split_ifs at hh hb' with hs
    · have hcN := of_decide_eq_true hh
      have hc : (num i : ℝ) * r ≤ (den i : ℝ) * (windowCount S i m r + 1 : ℕ) := by
        exact_mod_cast hcN
      have hd : (den i : ℝ) < (num i : ℝ) * a i := by
        have := (div_lt_iff₀ hn).mp hb'
        nlinarith
      calc
        _ ≤ (den i : ℝ) * (windowCount S i m r + 1 : ℕ) := hc
        _ < ((num i : ℝ) * a i) * (windowCount S i m r + 1 : ℕ) :=
          mul_lt_mul_of_pos_right hd hC
        _ = _ := by ring
    · have hcN := of_decide_eq_true hh
      have hc : (num i : ℝ) * r < (den i : ℝ) * (windowCount S i m r + 1 : ℕ) := by
        exact_mod_cast hcN
      have hd : (den i : ℝ) ≤ (num i : ℝ) * a i := by
        have := (div_le_iff₀ hn).mp hb'
        nlinarith
      calc
        _ < (den i : ℝ) * (windowCount S i m r + 1 : ℕ) := hc
        _ ≤ ((num i : ℝ) * a i) * (windowCount S i m r + 1 : ℕ) :=
          mul_le_mul_of_nonneg_right hd hC.le
        _ = _ := by ring
