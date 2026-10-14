-- Prove2me | solution 1 for SingleMachinePrec.IntervalReduction.remark_7_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:19:28.967422+00:00
-- url     : https://prove2.me/submissions/9f9aad45-b400-4418-8c70-28530c227685

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

theorem remark_core {N : ℕ} {G : SimpleGraph (Fin N)} (L : TreeLayout G) (k : ℝ) (hk : 1 < k)
    (x y : Job L) (hxy : left L x ≤ right L y) :
    procTime L k x ≤ 1 / k ^ ⌈right L x⌉ ∧
    weight L k y ≤ k ^ ⌈left L y⌉ ∧
    (Incomparable (prec L) x y →
      procTime L k x * weight L k y = 1 ∨ procTime L k x * weight L k y ≤ 1 / k) ∧
    (k ≤ procTime L k x * weight L k y → right L x < left L y) ∧
    (procTime L k x * weight L k y = 1 → ⌈right L x⌉ = ⌈left L y⌉) := by
  refine ⟨procTime_le L k hk x, weight_le L k hk y, ?_, ?_, ?_⟩
  · intro hinc
    have h1 : ¬ right L x < left L y := fun h => hinc.1 (Or.inr h)
    have h2 : left L y ≤ right L x := not_lt.mp h1
    by_cases he : ⌈left L y⌉ = ⌈right L x⌉
    · rcases prod_cases L k hk x y with h0 | h0
      · right; rw [h0]; positivity
      · left; rw [h0, he]; simp
    · right; exact prod_le_inv_of L k hk x y h2 he
  · intro hk'
    by_contra hcon
    have := prod_le_one_of L k hk x y (not_lt.mp hcon)
    linarith
  · intro h; exact (prod_eq_one_iff L k hk x y h).symm

end SingleMachinePrec.IntervalReduction

open SingleMachinePrec.IntervalReduction


theorem solution {N : ℕ} {G : SimpleGraph (Fin N)} (L : TreeLayout G) (k : ℝ) (hk : 1 < k)
    (x y : Job L) (hxy : left L x ≤ right L y) :
    procTime L k x ≤ 1 / k ^ ⌈right L x⌉ ∧
    weight L k y ≤ k ^ ⌈left L y⌉ ∧
    (Incomparable (prec L) x y →
      procTime L k x * weight L k y = 1 ∨ procTime L k x * weight L k y ≤ 1 / k) ∧
    (k ≤ procTime L k x * weight L k y → right L x < left L y) ∧
    (procTime L k x * weight L k y = 1 → ⌈right L x⌉ = ⌈left L y⌉) := by
  exact remark_core L k hk x y hxy
