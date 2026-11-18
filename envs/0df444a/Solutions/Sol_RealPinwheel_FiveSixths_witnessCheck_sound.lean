-- Prove2me | solution 1 for RealPinwheel.FiveSixths.witnessCheck_sound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T03:48:26.438164+00:00
-- url     : https://prove2.me/submissions/28f260de-c5b8-4190-a38d-b4999d690dc2

import Definitions.Def_RealPinwheel_FiveSixths_Witness
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

private theorem discrepancy_bound {n L : ℕ} (S : ℕ → Fin n) (hL : 0 < L)
    (hper : ∀ t, S (t + L) = S t) (i : Fin n) (num den : ℕ) (cap : ℤ)
    (lo hi : Fin L → ℤ)
    (hlo : Antitone lo) (hhi : Monotone hi)
    (hbound : ∀ t : Fin L,
      let d : ℤ := (num : ℤ) * t.val - (den : ℤ) * Nat.count (fun s => S s = i) t.val
      lo t ≤ d ∧ hi t ≤ d ∧ d - lo t ≤ cap ∧
      d + ((num : ℤ) * L - (den : ℤ) * Nat.count (fun s => S s = i) L) - hi t ≤ cap) :
    ∀ m r : ℕ, m < L → r < L →
      (num : ℤ) * r - (den : ℤ) * windowCount S i m r ≤ cap := by
  intro m r hm hr
  let p := Nat.count (fun s => S s = i)
  let D := fun t : ℕ => (num : ℤ) * t - (den : ℤ) * p t
  let drift : ℤ := (num : ℤ) * L - (den : ℤ) * p L
  have he : D (m + r) - D m = (num : ℤ) * r - (den : ℤ) * windowCount S i m r := by
    dsimp [D, p]
    rw [prefix_window]
    push_cast
    ring
  rw [← he]
  by_cases hmr : m + r < L
  · have h1 := hbound ⟨m + r, hmr⟩
    have h2 := hbound ⟨m, hm⟩
    have hh : lo ⟨m + r, hmr⟩ ≤ lo ⟨m, hm⟩ := hlo (by simp)
    change lo ⟨m + r, hmr⟩ ≤ D (m + r) ∧ hi ⟨m + r, hmr⟩ ≤ D (m + r) ∧
      D (m + r) - lo ⟨m + r, hmr⟩ ≤ cap ∧ _ at h1
    change lo ⟨m, hm⟩ ≤ D m ∧ _ at h2
    omega
  · have ht : m + r - L < L := by omega
    let t : Fin L := ⟨m + r - L, ht⟩
    have hp := periodic_prefix S L hper i t.val
    have hval : t.val + L = m + r := by dsimp [t]; omega
    rw [hval] at hp
    have hD : D (m + r) = D t.val + drift := by
      dsimp [D, drift, p]
      rw [hp]
      have hh : ((m + r : ℕ) : ℤ) = (t.val : ℤ) + L := by exact_mod_cast hval.symm
      push_cast at hh ⊢
      nlinarith [congrArg (fun z : ℤ => (num : ℤ) * z) hh]
    have h1 := hbound t
    have h2 := hbound ⟨m, hm⟩
    have hh : hi t ≤ hi ⟨m, hm⟩ := hhi (by change t.val ≤ m; dsimp [t]; omega)
    change _ ∧ _ ∧ _ ∧ D t.val + drift - hi t ≤ cap at h1
    change _ ∧ hi ⟨m, hm⟩ ≤ D m ∧ _ at h2
    rw [hD]
    omega

private lemma mono_steps {L : ℕ} (f : Fin L → ℤ)
    (h : ∀ t : Fin L, ∀ ht : t.val + 1 < L, f t ≤ f ⟨t.val + 1, ht⟩) : Monotone f := by
  cases L with
  | zero => intro i; exact Fin.elim0 i
  | succ L =>
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact h i.castSucc i.succ.isLt

private lemma anti_steps {L : ℕ} (f : Fin L → ℤ)
    (h : ∀ t : Fin L, ∀ ht : t.val + 1 < L, f ⟨t.val + 1, ht⟩ ≤ f t) : Antitone f := by
  cases L with
  | zero => intro i; exact Fin.elim0 i
  | succ L =>
    apply Fin.antitone_iff_succ_le.mpr
    intro i
    exact h i.castSucc i.succ.isLt


private lemma witness_bounds {n : ℕ} (hn : 0 < n) (w : CycleWitness n)
    (hc : witnessCheck w = true) :
    0 < w.length ∧ ∀ i : Fin n,
      0 < codeNum w.code i ∧ 0 < codeDen w.code i ∧
      codeNum w.code i * w.length ≤ codeDen w.code i * windowCount (witnessSchedule hn w) i 0 w.length ∧
      ∀ m r : ℕ, m < w.length → r < w.length →
        (codeNum w.code i : ℤ) * r - (codeDen w.code i : ℤ) * windowCount (witnessSchedule hn w) i m r ≤
          (codeDen w.code i : ℤ) - if codeStrict w.code i then 0 else 1 := by
  simp only [witnessCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, forall_true_left, List.mem_range] at hc
  refine ⟨hc.1, ?_⟩
  intro i
  have hi := hc.2 i
  let S := witnessSchedule hn w
  let p := fun t => (w.counts i).eval t
  have hp (t : ℕ) (ht : t ≤ w.length) : p t = Nat.count (fun s => S s = i) t := by
    induction t with
    | zero => exact hi.1.2.2.1
    | succ t ih =>
      have hstep := (hi.2 t (by omega)).1.1
      have ht' : t % w.length = t := Nat.mod_eq_of_lt (by omega)
      have he : w.word.eval t % n = i.val ↔ S t = i := by
        simp only [S, witnessSchedule, ht', Fin.ext_iff]
      change p (t + 1) = p t + (if w.word.eval t % n = i.val then 1 else 0) at hstep
      simp only [he, ih (by omega)] at hstep
      simpa only [Nat.count_succ] using hstep
  have hcount : p w.length = windowCount S i 0 w.length := by
    rw [hp _ le_rfl]
    simp [windowCount_count]
  refine ⟨hi.1.1, hi.1.2.1, ?_, ?_⟩
  · have hh := hi.1.2.2.2
    change codeNum w.code i * w.length ≤ codeDen w.code i * p w.length at hh
    rw [hcount] at hh
    exact hh
  · intro m r hm hr
    let lo : Fin w.length → ℤ := fun t => (w.low i).eval t.val
    let high : Fin w.length → ℤ := fun t => (w.high i).eval t.val
    have hsteps (t : Fin w.length) (ht : t.val + 1 < w.length) :
        lo ⟨t.val + 1, ht⟩ ≤ lo t ∧ high t ≤ high ⟨t.val + 1, ht⟩ := by
      have hh := (hi.2 t.val t.isLt).2
      simpa only [if_pos ht, decide_eq_true_eq] using hh
    have hlo : Antitone lo := anti_steps lo fun t ht => (hsteps t ht).1
    have hhi : Monotone high := mono_steps high fun t ht => (hsteps t ht).2
    have hbd (t : Fin w.length) :
        let d : ℤ := (codeNum w.code i : ℤ) * t.val -
          (codeDen w.code i : ℤ) * Nat.count (fun s => S s = i) t.val
        lo t ≤ d ∧ high t ≤ d ∧
          d - lo t ≤ (codeDen w.code i : ℤ) - (if codeStrict w.code i then 0 else 1) ∧
          d + ((codeNum w.code i : ℤ) * w.length -
            (codeDen w.code i : ℤ) * Nat.count (fun s => S s = i) w.length) - high t ≤
              (codeDen w.code i : ℤ) - (if codeStrict w.code i then 0 else 1) := by
      have hh := (hi.2 t.val t.isLt).1.2
      rw [← hp t.val (by omega), ← hp w.length le_rfl]
      exact hh
    have hper : ∀ t, S (t + w.length) = S t := by
      intro t
      simp [S, witnessSchedule]
    exact discrepancy_bound S hc.1 hper i (codeNum w.code i) (codeDen w.code i)
      ((codeDen w.code i : ℤ) - if codeStrict w.code i then 0 else 1)
      lo high hlo hhi hbd m r hm hr

theorem solution {n : ℕ} (hn : 0 < n) (w : CycleWitness n)
    (hc : witnessCheck w = true) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (hb : codeBox w.code (fun i => 1 / a i)) :
    ∃ (L : ℕ) (S : ℕ → Fin n), L = w.length ∧ Periodic S L ∧ Valid a S := by
  obtain ⟨hL, hbounds⟩ := witness_bounds hn w hc
  let S := witnessSchedule hn w
  have hper : ∀ t, S (t + w.length) = S t := by intro t; simp [S, witnessSchedule]
  refine ⟨w.length, S, rfl, ⟨hL, hper⟩, ?_⟩
  have hperiod (i : Fin n) :
      if codeStrict w.code i then (codeDen w.code i : ℝ) < (codeNum w.code i : ℝ) * a i
      else (codeDen w.code i : ℝ) ≤ (codeNum w.code i : ℝ) * a i := by
    have hh := hb i
    have hq : (0 : ℝ) < codeDen w.code i := by exact_mod_cast (hbounds i).2.1
    change (if codeStrict w.code i = true then 1 / a i < (codeNum w.code i : ℝ) / codeDen w.code i
      else 1 / a i ≤ (codeNum w.code i : ℝ) / codeDen w.code i) at hh
    split_ifs at hh ⊢ with hs
    · have h := (div_lt_div_iff₀ (ha i) hq).mp hh
      simpa using h
    · have h := (div_le_div_iff₀ (ha i) hq).mp hh
      simpa using h
  apply finiteWindow_valid S w.length hL hper a ha
  · intro i
    have hn' : (0 : ℝ) < codeNum w.code i := by exact_mod_cast (hbounds i).1
    have hd : (codeDen w.code i : ℝ) ≤ (codeNum w.code i : ℝ) * a i := by
      have hh := hperiod i
      split_ifs at hh
      · exact hh.le
      · exact hh
    have hm : (codeNum w.code i : ℝ) * w.length ≤
        (codeDen w.code i : ℝ) * windowCount S i 0 w.length := by
      exact_mod_cast (hbounds i).2.2.1
    apply (mul_le_mul_iff_right₀ hn').mp
    calc
      _ ≤ (codeDen w.code i : ℝ) * windowCount S i 0 w.length := hm
      _ ≤ ((codeNum w.code i : ℝ) * a i) * windowCount S i 0 w.length :=
        mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg _)
      _ = _ := by ring
  · intro i m r hm hr
    have hw := (hbounds i).2.2.2 m r hm hr
    have hn' : (0 : ℝ) < codeNum w.code i := by exact_mod_cast (hbounds i).1
    have hC : (0 : ℝ) < (windowCount S i m r + 1 : ℕ) := by positivity
    have hd := hperiod i
    apply (mul_lt_mul_iff_right₀ hn').mp
    split_ifs at hd with hs
    · simp [hs] at hw
      have hh : codeNum w.code i * r ≤ codeDen w.code i * (windowCount S i m r + 1) := by
        have he : (codeNum w.code i : ℤ) * r ≤ (codeDen w.code i : ℤ) * (windowCount S i m r + 1) := by
          push_cast
          nlinarith
        exact_mod_cast he
      have hhR : (codeNum w.code i : ℝ) * r ≤ (codeDen w.code i : ℝ) * (windowCount S i m r + 1 : ℕ) := by exact_mod_cast hh
      calc
        _ ≤ (codeDen w.code i : ℝ) * (windowCount S i m r + 1 : ℕ) := hhR
        _ < ((codeNum w.code i : ℝ) * a i) * (windowCount S i m r + 1 : ℕ) := mul_lt_mul_of_pos_right hd hC
        _ = _ := by ring
    · simp [hs] at hw
      have hh : codeNum w.code i * r < codeDen w.code i * (windowCount S i m r + 1) := by
        have he : (codeNum w.code i : ℤ) * r < (codeDen w.code i : ℤ) * (windowCount S i m r + 1) := by
          push_cast
          nlinarith
        exact_mod_cast he
      have hhR : (codeNum w.code i : ℝ) * r < (codeDen w.code i : ℝ) * (windowCount S i m r + 1 : ℕ) := by exact_mod_cast hh
      calc
        _ < (codeDen w.code i : ℝ) * (windowCount S i m r + 1 : ℕ) := hhR
        _ ≤ ((codeNum w.code i : ℝ) * a i) * (windowCount S i m r + 1 : ℕ) := mul_le_mul_of_nonneg_right hd hC.le
        _ = _ := by ring
