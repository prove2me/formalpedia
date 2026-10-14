-- Prove2me | solution 1 for SingleMachinePrec.IntervalReduction.claim_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:21:42.456734+00:00
-- url     : https://prove2.me/submissions/d0283adc-a9a8-4c9b-aa43-95939065f553

import Mathlib
import Definitions.Def_SingleMachinePrec_IntervalReduction_Instance



namespace SingleMachinePrec.IntervalReduction

variable {N : ℕ} {G : SimpleGraph (Fin N)}

lemma ceil_nat_cast_sub_half (n : ℕ) (hn : 1 ≤ n) : ⌈((n : ℝ) - 1 / 2)⌉ = (n : ℤ) := by
  rw [Int.ceil_eq_iff]
  constructor
  · push_cast; linarith
  · push_cast; linarith

lemma ceil_right (L : TreeLayout G) (x : Job L) :
    ⌈right L x⌉ = match x with
      | .s0 => 0
      | .s j => (num j : ℤ)
      | .m i => ((N + num i : ℕ) : ℤ)
      | .e i => ((N + num i + 1 : ℕ) : ℤ)
      | .b q => (num q.1.2 : ℤ) := by
  cases x with
  | s0 => simp [right]
  | s j => simp only [right]; exact Int.ceil_natCast _
  | m i =>
    simp only [right]
    rw [← Int.ceil_natCast (R := ℝ) (N + num i)]; push_cast; rfl
  | e i =>
    simp only [right]
    rw [← Int.ceil_natCast (R := ℝ) (N + num i + 1)]; push_cast; rfl
  | b q =>
    simp only [right]
    exact ceil_nat_cast_sub_half _ (by simp [num])

lemma ceil_left (L : TreeLayout G) (x : Job L) :
    ⌈left L x⌉ = match x with
      | .s0 => -1
      | .s j => (parNum L j : ℤ)
      | .m i => (num i : ℤ)
      | .e i => ((N + num i : ℕ) : ℤ)
      | .b q => (num q.1.1 : ℤ) := by
  cases x with
  | s0 => simp only [left]; exact Int.ceil_eq_iff.mpr (by norm_num)
  | s j => simp only [left]; exact Int.ceil_natCast _
  | m i =>
    simp only [left]
    exact ceil_nat_cast_sub_half _ (by simp [num])
  | e i =>
    simp only [left]
    rw [← Int.ceil_natCast (R := ℝ) (N + num i)]; push_cast; rfl
  | b q => simp only [left]; exact Int.ceil_natCast _

lemma procTime_cases (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x : Job L) :
    procTime L k x = 0 ∨ procTime L k x = k ^ (-⌈right L x⌉) := by
  have hk0 : k ≠ 0 := by positivity
  rw [ceil_right]
  cases x with
  | s0 => right; simp [procTime]
  | s j => right; simp [procTime, zpow_neg]
  | m i => right; simp only [procTime]; rw [one_div, ← zpow_natCast, ← zpow_neg]
  | e i => left; simp [procTime]
  | b q => right; simp [procTime, zpow_neg]

lemma weight_cases (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x : Job L) :
    weight L k x = 0 ∨ weight L k x = k ^ ⌈left L x⌉ := by
  have hk0 : k ≠ 0 := by positivity
  rw [ceil_left]
  cases x with
  | s0 => left; simp [weight]
  | s j => right; simp [weight]
  | m i => right; simp [weight]
  | e i => right; simp only [weight]; exact (zpow_natCast _ _).symm
  | b q => right; simp [weight]

lemma procTime_le (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x : Job L) :
    procTime L k x ≤ 1 / k ^ ⌈right L x⌉ := by
  have hk0 : 0 < k := by positivity
  rcases procTime_cases L k hk x with h | h
  · rw [h]; positivity
  · rw [h, zpow_neg, one_div]

lemma weight_le (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x : Job L) :
    weight L k x ≤ k ^ ⌈left L x⌉ := by
  have hk0 : 0 < k := by positivity
  rcases weight_cases L k hk x with h | h
  · rw [h]; positivity
  · rw [h]

lemma prod_cases (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x y : Job L) :
    procTime L k x * weight L k y = 0 ∨
      procTime L k x * weight L k y = k ^ (⌈left L y⌉ - ⌈right L x⌉) := by
  have hk0 : k ≠ 0 := by positivity
  rcases procTime_cases L k hk x with h | h
  · left; rw [h]; simp
  rcases weight_cases L k hk y with h' | h'
  · left; rw [h']; simp
  · right; rw [h, h', ← zpow_add₀ hk0]; congr 1; ring

lemma prod_le_one_of (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x y : Job L)
    (h : left L y ≤ right L x) :
    procTime L k x * weight L k y ≤ 1 := by
  have hle : ⌈left L y⌉ ≤ ⌈right L x⌉ := Int.ceil_le_ceil h
  rcases prod_cases L k hk x y with h0 | h0
  · rw [h0]; norm_num
  · rw [h0]; exact zpow_le_one_of_nonpos₀ hk.le (by omega)

lemma prod_le_inv_of (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x y : Job L)
    (h : left L y ≤ right L x) (h' : ⌈left L y⌉ ≠ ⌈right L x⌉) :
    procTime L k x * weight L k y ≤ 1 / k := by
  have hk0 : 0 < k := by positivity
  have hle : ⌈left L y⌉ ≤ ⌈right L x⌉ := Int.ceil_le_ceil h
  rcases prod_cases L k hk x y with h0 | h0
  · rw [h0]; positivity
  · rw [h0, one_div, ← zpow_neg_one]
    exact zpow_le_zpow_right₀ hk.le (by omega)

lemma prod_eq_one_iff (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x y : Job L)
    (h : procTime L k x * weight L k y = 1) : ⌈left L y⌉ = ⌈right L x⌉ := by
  rcases prod_cases L k hk x y with h0 | h0
  · rw [h0] at h; norm_num at h
  · rw [h0] at h
    have := (zpow_eq_one_iff_right₀ (by linarith) hk.ne').mp h
    omega


lemma parNum_eq_zero (L : TreeLayout G) (j : Fin N) : parNum L j = 0 ↔ L.par j = none := by
  unfold parNum
  cases h : L.par j <;> simp

lemma parNum_eq_num (L : TreeLayout G) (j i : Fin N) : parNum L j = num i ↔ L.par j = some i := by
  unfold parNum num
  cases h : L.par j with
  | none => simp
  | some i' => simp [Fin.ext_iff]

lemma parNum_lt (L : TreeLayout G) (j : Fin N) : parNum L j < N := by
  unfold parNum
  cases h : L.par j with
  | none => simp; exact lt_of_le_of_lt (Nat.zero_le _) j.2
  | some i' =>
    have := L.par_lt j i' h
    have h2 : i'.val < j.val := this
    have := j.2
    simp; omega

lemma num_le (i : Fin N) : num i ≤ N := by unfold num; have := i.2; omega
lemma num_pos (i : Fin N) : 1 ≤ num i := by unfold num; omega
lemma num_inj {i j : Fin N} : num i = num j ↔ i = j := by
  unfold num; simp [Fin.ext_iff]

lemma InD_key (L : TreeLayout G) (x y : Job L) (hinc : Incomparable (prec L) x y)
    (hceil : ⌈left L y⌉ = ⌈right L x⌉) (hx : ∀ i, x ≠ .e i) (hy : y ≠ .s0) : InD L x y := by
  rw [ceil_left, ceil_right] at hceil
  cases x with
  | s0 =>
    cases y with
    | s0 => exact absurd rfl hy
    | s j => simp only [InD]; simp at hceil; exact (parNum_eq_zero L j).mp (by omega)
    | m i => simp at hceil; have := num_pos i; omega
    | e i => simp at hceil; have := num_pos i; omega
    | b q => simp at hceil; have := num_pos q.1.1; omega
  | s j =>
    have h1 := num_le j
    cases y with
    | s0 => exact absurd rfl hy
    | s j' => simp only [InD]; simp at hceil; exact (parNum_eq_num L j' j).mp (by omega)
    | m i => simp at hceil; simp only [InD]; exact (num_inj.mp (by omega)).symm
    | e i => simp at hceil; have := num_pos i; omega
    | b q => simp at hceil; simp only [InD]; exact num_inj.mp (by omega)
  | m i =>
    have h1 := num_le i
    cases y with
    | s0 => exact absurd rfl hy
    | s j' => simp at hceil; have := parNum_lt L j'; omega
    | m i' => simp at hceil; have := num_le i'; have := num_pos i; omega
    | e i' => simp at hceil; simp only [InD]; exact (num_inj.mp (by omega))
    | b q => simp at hceil; have := num_le q.1.1; have := num_pos i; omega
  | e i => exact absurd rfl (hx i)
  | b q =>
    have h1 := num_le q.1.2
    have h2 : (1:ℕ) ≤ num q.1.2 := num_pos _
    cases y with
    | s0 => exact absurd rfl hy
    | s j' =>
      simp at hceil
      exfalso; apply hinc.1; right
      simp only [right, left]
      have : (parNum L j' : ℝ) = num q.1.2 := by exact_mod_cast hceil
      rw [this]; linarith
    | m i' => simp at hceil; simp only [InD]; exact num_inj.mp (by omega)
    | e i' => simp at hceil; have := num_pos i'; omega
    | b q' =>
      simp at hceil
      exfalso; apply hinc.1; right
      simp only [right, left]
      have : (num q'.1.1 : ℝ) = num q.1.2 := by exact_mod_cast hceil
      rw [this]; linarith

lemma claim2_core (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x y : Job L)
    (hxy : Incomparable (prec L) x y) :
    (InD L x y → procTime L k x * weight L k y = 1) ∧
    (¬ InD L x y → procTime L k x * weight L k y ≤ 1 / k) := by
  have hk0 : k ≠ 0 := by positivity
  constructor
  · intro h
    cases x <;> cases y <;> simp only [InD] at h <;> try contradiction
    · simp [procTime, weight, (parNum_eq_zero L _).mpr h]
    · have := (parNum_eq_num L _ _).mpr h
      simp only [procTime, weight, this]
      field_simp
    all_goals (subst h; simp only [procTime, weight]; field_simp)
  · intro h
    by_cases hx : ∃ i, x = .e i
    · obtain ⟨i, rfl⟩ := hx
      simp [procTime]; positivity
    by_cases hy : y = .s0
    · subst hy; simp [weight]; positivity
    push_neg at hx
    have hle : left L y ≤ right L x := not_lt.mp (fun h => hxy.1 (Or.inr h))
    refine prod_le_inv_of L k hk x y hle ?_
    intro he
    exact h (InD_key L x y hxy he hx hy)

end SingleMachinePrec.IntervalReduction

open SingleMachinePrec.IntervalReduction


theorem solution {N : ℕ} {G : SimpleGraph (Fin N)} (L : TreeLayout G) (k : ℝ) (hk : 1 < k)
    (x y : Job L) (hxy : Incomparable (prec L) x y) :
    (InD L x y → procTime L k x * weight L k y = 1) ∧
    (¬ InD L x y → procTime L k x * weight L k y ≤ 1 / k) := by
  exact claim2_core L k hk x y hxy
