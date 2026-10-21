-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P21.units_and_nonnegative_squares
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T22:45:59.350733+00:00
-- url     : https://prove2.me/submissions/4d5126c4-c8ce-49df-b440-06ab5b27c499

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21
noncomputable section
open QAlgorithms.Papers.Independent.Next46.P21
open Set
open scoped ComplexConjugate Matrix

theorem g64a_qr (a : Zsqrtd 2) : quadraticReal a = (a.re : ℝ) + (a.im : ℝ) * Real.sqrt 2 := by
  simp [quadraticReal, Zsqrtd.toReal_apply]

theorem g64a_s2 : (1.41 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.42 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem g64a_mapz (f : Zsqrtd 2 →+* ℝ) (w : (Zsqrtd 2)ˣ) (k : ℤ) :
    f ((w ^ k : (Zsqrtd 2)ˣ) : Zsqrtd 2) = (f (w : Zsqrtd 2)) ^ k := by
  have h := congrArg Units.val (map_zpow (Units.map (f : Zsqrtd 2 →* ℝ)) w k)
  rw [Units.val_zpow_eq_zpow_val, Units.coe_map, Units.coe_map] at h
  exact h

theorem g64a_normpm (u : Zsqrtd 2) (hu : IsUnit u) :
    (u.re : ℝ) ^ 2 - 2 * (u.im : ℝ) ^ 2 = 1 ∨ (u.re : ℝ) ^ 2 - 2 * (u.im : ℝ) ^ 2 = -1 := by
  rw [← Zsqrtd.norm_eq_one_iff, Int.natAbs_eq_iff, Zsqrtd.norm_def] at hu
  rcases hu with h | h
  · left; have : ((u.re * u.re - 2 * u.im * u.im : ℤ) : ℝ) = 1 := by exact_mod_cast h
    push_cast at this; linarith
  · right; have : ((u.re * u.re - 2 * u.im * u.im : ℤ) : ℝ) = -1 := by exact_mod_cast h
    push_cast at this; linarith

theorem g64a_core (V : Zsqrtd 2) (hV : IsUnit V) (h1 : 1 ≤ quadraticReal V)
    (h2 : quadraticReal V < 1 + Real.sqrt 2) : V = 1 := by
  obtain ⟨s1, s2⟩ := g64a_s2
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  rw [g64a_qr] at h1 h2
  obtain ⟨x, y⟩ := V
  have hn := g64a_normpm _ hV
  simp only at hn h1 h2
  set p : ℝ := x + y * Real.sqrt 2 with hp
  set q : ℝ := x - y * Real.sqrt 2 with hq
  have hpq : p * q = 1 ∨ p * q = -1 := by
    rcases hn with h | h
    · left; rw [hp, hq]; nlinarith
    · right; rw [hp, hq]; nlinarith
  have hq1 : q ≤ 1 := by
    by_contra h; push Not at h
    rcases hpq with h' | h' <;> nlinarith
  have hq2 : -1 ≤ q := by
    by_contra h; push Not at h
    rcases hpq with h' | h' <;> nlinarith
  have hx0 : (-1:ℝ) < x := by linarith
  have hx1 : (x:ℝ) < 2 := by linarith
  have hy0 : (-1:ℝ) < y := by
    by_contra h; push Not at h; nlinarith
  have hy1 : (y:ℝ) < 2 := by
    by_contra h; push Not at h; nlinarith
  have : (-1:ℤ) < x := by exact_mod_cast hx0
  have : x < (2:ℤ) := by exact_mod_cast hx1
  have : (-1:ℤ) < y := by exact_mod_cast hy0
  have : y < (2:ℤ) := by exact_mod_cast hy1
  interval_cases x <;> interval_cases y
  all_goals first | rfl | (exfalso; simp only [hp, hq] at h1 h2 hq1 hq2; push_cast at h1 h2 hq1 hq2; nlinarith)

theorem g64a_small : quadraticReal (smallUnit : Zsqrtd 2) = Real.sqrt 2 - 1 := by
  rw [g64a_qr]; simp [smallUnit]; ring

theorem g64a_small_star : quadraticReal (star (smallUnit : Zsqrtd 2)) = -(1 + Real.sqrt 2) := by
  rw [g64a_qr]; simp [smallUnit]; ring

theorem g64a_pos (U : (Zsqrtd 2)ˣ) (hU : 0 < quadraticReal (U : Zsqrtd 2)) :
    ∃ k : ℤ, U = smallUnit ^ k := by
  obtain ⟨s1, s2⟩ := g64a_s2
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  set μ : ℝ := 1 + Real.sqrt 2 with hμ
  have hμ1 : 1 < μ := by linarith
  have hμ0 : 0 < μ := by linarith
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hU hμ1
  set V := U * smallUnit ^ n with hV
  have hc : (Real.sqrt 2 - 1) ^ n * μ ^ n = 1 := by
    rw [← mul_zpow]
    have : (Real.sqrt 2 - 1) * μ = 1 := by rw [hμ]; nlinarith
    rw [this, one_zpow]
  have hμn : 0 < μ ^ n := zpow_pos hμ0 n
  have hφV : quadraticReal (V : Zsqrtd 2) = quadraticReal (U : Zsqrtd 2) / μ ^ n := by
    rw [hV, Units.val_mul, map_mul, g64a_mapz, g64a_small, eq_div_iff hμn.ne', mul_assoc, hc,
      mul_one]
  have hV1 : (V : Zsqrtd 2) = 1 := by
    apply g64a_core _ V.isUnit
    · rw [hφV, le_div_iff₀ hμn]; linarith
    · have h3 := hn2
      rw [zpow_add_one₀ hμ0.ne'] at h3
      have e : (1 + Real.sqrt 2) * μ ^ n = μ ^ n * μ := by rw [hμ]; ring
      rw [hφV, div_lt_iff₀ hμn]; linarith
  have hV1' : V = 1 := Units.ext hV1
  refine ⟨-n, ?_⟩
  rw [zpow_neg]
  exact eq_inv_of_mul_eq_one_left hV1'

theorem g64a_units (u : Zsqrtd 2) : IsUnit u ↔ ∃ n k : ℤ,
      u = ((((-1 : (Zsqrtd 2)ˣ) ^ n) * smallUnit ^ k : (Zsqrtd 2)ˣ) : Zsqrtd 2) := by
  constructor
  · rintro ⟨U, rfl⟩
    have hne : quadraticReal (U : Zsqrtd 2) ≠ 0 := by
      intro h
      have : (U : Zsqrtd 2) = 0 := by
        have := (map_eq_zero_iff quadraticReal (Zsqrtd.toReal_injective (by norm_num) (by
          intro n hn
          have h1 : n.natAbs * n.natAbs = 2 := by
            have := congrArg Int.natAbs hn; simpa [Int.natAbs_mul] using this.symm
          have : n.natAbs ≤ 2 := by nlinarith
          interval_cases (n.natAbs) <;> omega))).1 h
        exact this
      exact U.ne_zero this
    rcases hne.lt_or_gt with h | h
    · obtain ⟨k, hk⟩ := g64a_pos (-U) (by rw [Units.val_neg, map_neg]; linarith)
      refine ⟨1, k, ?_⟩
      rw [← hk]; simp
    · obtain ⟨k, hk⟩ := g64a_pos U h
      exact ⟨0, k, by rw [hk]; simp⟩
  · rintro ⟨n, k, rfl⟩
    exact Units.isUnit _

theorem g64a_sq (u : Zsqrtd 2) (hu : IsUnit u) :
    ((∃ v : Zsqrtd 2, v ^ 2 = u) ↔
        0 ≤ quadraticReal u ∧ 0 ≤ quadraticReal (star u)) := by
  constructor
  · rintro ⟨v, rfl⟩
    rw [star_pow, map_pow, map_pow]
    exact ⟨sq_nonneg _, sq_nonneg _⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨n, k, rfl⟩ := (g64a_units u).1 hu
    obtain ⟨s1, s2⟩ := g64a_s2
    set φ' : Zsqrtd 2 →+* ℝ := quadraticReal.comp (starRingEnd (Zsqrtd 2)) with hφ'
    have hφ'x : ∀ x, φ' x = quadraticReal (star x) := fun x => rfl
    rw [Units.val_mul, map_mul, g64a_mapz, g64a_mapz, g64a_small] at h1
    rw [← hφ'x, Units.val_mul, map_mul, g64a_mapz, g64a_mapz, hφ'x, hφ'x, g64a_small_star] at h2
    simp only [Units.val_neg, Units.val_one, star_neg, star_one, map_neg, map_one] at h1 h2
    have hc : 0 < (Real.sqrt 2 - 1) ^ k := zpow_pos (by linarith) k
    have hm : 0 < (1 + Real.sqrt 2) ^ k := zpow_pos (by linarith) k
    rcases Int.even_or_odd n with hn | hn
    · rw [hn.neg_one_zpow, one_mul] at h2
      rcases Int.even_or_odd k with hk | hk
      · obtain ⟨j, rfl⟩ := hk
        refine ⟨((smallUnit ^ j : (Zsqrtd 2)ˣ) : Zsqrtd 2), ?_⟩
        rw [hn.neg_one_zpow, one_mul, zpow_add, Units.val_mul, sq]
      · rw [hk.neg_zpow] at h2; linarith
    · rw [hn.neg_one_zpow] at h1; linarith

theorem solution :
    (∀ u : Zsqrtd 2, IsUnit u ↔ ∃ n k : ℤ,
      u = ((((-1 : (Zsqrtd 2)ˣ) ^ n) * smallUnit ^ k : (Zsqrtd 2)ˣ) : Zsqrtd 2)) ∧
    (∀ u : Zsqrtd 2, IsUnit u →
      ((∃ v : Zsqrtd 2, v ^ 2 = u) ↔
        0 ≤ quadraticReal u ∧ 0 ≤ quadraticReal (star u))) :=
  ⟨g64a_units, g64a_sq⟩
