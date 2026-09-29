-- Prove2me | solution 1 for PlanckUnits.derived_planck_units
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T20:03:52.644729+00:00
-- url     : https://prove2.me/submissions/e09fe162-fce8-4287-b27c-ab67686ba6b5

import Definitions.Def_planck_units

open PlanckUnits

theorem W2p_PlanckUnits_sqrt_eq (x y : ℝ) (hy : 0 ≤ y) (h : y ^ 2 = x) :
    Real.sqrt x = y := by
  rw [← h]; exact Real.sqrt_sq hy

theorem W2p_PlanckUnits_repr (c G hbar : ℝ) (hc : 0 < c) (hG : 0 < G) (hh : 0 < hbar) :
    ∃ T : ℝ, 0 < T ∧ Real.sqrt (hbar * G / c ^ 5) = T ∧ hbar = T ^ 2 * c ^ 5 / G ∧
      Real.sqrt (hbar * G / c ^ 3) = c * T ∧ Real.sqrt (hbar * c / G) = c ^ 3 * T / G ∧
      Real.sqrt (hbar * c ^ 5 / G) = c ^ 5 * T / G := by
  have hT2 : Real.sqrt (hbar * G / c ^ 5) ^ 2 = hbar * G / c ^ 5 :=
    Real.sq_sqrt (by positivity)
  have hc0 := hc.ne'
  have hG0 := hG.ne'
  refine ⟨Real.sqrt (hbar * G / c ^ 5), Real.sqrt_pos.mpr (by positivity), rfl, ?_, ?_, ?_, ?_⟩
  · rw [hT2]; field_simp <;> ring
  · apply W2p_PlanckUnits_sqrt_eq _ _ (by positivity)
    rw [mul_pow, hT2]; field_simp <;> ring
  · apply W2p_PlanckUnits_sqrt_eq _ _ (by positivity)
    rw [div_pow, mul_pow, hT2]; field_simp <;> ring
  · apply W2p_PlanckUnits_sqrt_eq _ _ (by positivity)
    rw [div_pow, mul_pow, hT2]; field_simp <;> ring

theorem W2p_PlanckUnits_planck_system_normalizes (c G hbar kB : ℝ) (hc : 0 < c) (hG : 0 < G)
    (hh : 0 < hbar)
    (hk : 0 < kB) :
    (planckSystem c G hbar kB).IsPositive ∧
      (planckSystem c G hbar kB).Normalizes c G hbar kB := by
  obtain ⟨T, hT0, hTd, hħ, hL, hM, hTe⟩ := W2p_PlanckUnits_repr c G hbar hc hG hh
  have hc0 := hc.ne'
  have hG0 := hG.ne'
  have hT00 := hT0.ne'
  have hk0 := hk.ne'
  unfold UnitSystem.IsPositive UnitSystem.Normalizes
  simp only [planckSystem]
  rw [hTd, hL, hM, hTe, hħ]
  refine ⟨⟨by positivity, by positivity, by positivity, by positivity⟩, ?_, ?_, ?_, ?_⟩ <;>
    field_simp <;> ring

theorem W2p_PlanckUnits_planck_system_unique_of_normalizes (c G hbar kB : ℝ) (hc : 0 < c)
    (hG : 0 < G) (hh : 0 < hbar)
    (hk : 0 < kB) (u : UnitSystem) (hu : u.IsPositive) (hn : u.Normalizes c G hbar kB) :
    u = planckSystem c G hbar kB := by
  obtain ⟨T, hT0, hTd, hħ, hL, hM, hTe⟩ := W2p_PlanckUnits_repr c G hbar hc hG hh
  have hc0 := hc.ne'
  have hG0 := hG.ne'
  have hk0 := hk.ne'
  obtain ⟨l, m, t, θ⟩ := u
  simp only [UnitSystem.IsPositive, UnitSystem.Normalizes] at hu hn
  obtain ⟨hl, hm, ht, hθ⟩ := hu
  obtain ⟨h1, h2, h3, h4⟩ := hn
  have ht0 := ht.ne'
  have hlct : l = c * t := by rw [div_eq_iff ht0] at h1; exact h1
  subst hlct
  have hmt : m = c ^ 3 * t / G := by
    rw [div_eq_iff (by positivity)] at h2
    rw [eq_div_iff hG0]
    apply mul_left_cancel₀ (pow_ne_zero 2 ht0)
    linear_combination -h2
  subst hmt
  have hħ' : hbar = c ^ 5 * t ^ 2 / G := by rw [← h3]; field_simp <;> ring
  have htT : t = T := by
    rw [← hTd]
    exact (W2p_PlanckUnits_sqrt_eq _ _ ht.le (by rw [hħ']; field_simp <;> ring)).symm
  have hθ' : θ = c ^ 5 * t / G / kB := by
    rw [div_eq_iff (by positivity)] at h4
    rw [eq_div_iff hk0]
    apply mul_left_cancel₀ (pow_ne_zero 2 ht0)
    linear_combination -h4
  subst hθ'
  simp only [planckSystem, UnitSystem.mk.injEq]
  rw [hTd, hL, hM, hTe, htT]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem W2p_PlanckUnits_planck_units_existence_and_uniqueness (c G hbar kB : ℝ) (hc : 0 < c)
    (hG : 0 < G) (hh : 0 < hbar)
    (hk : 0 < kB) :
    (planckSystem c G hbar kB).IsPositive ∧
      (planckSystem c G hbar kB).Normalizes c G hbar kB ∧
      ∀ u : UnitSystem, u.IsPositive → u.Normalizes c G hbar kB →
        u = planckSystem c G hbar kB := by
  obtain ⟨h1, h2⟩ := W2p_PlanckUnits_planck_system_normalizes c G hbar kB hc hG hh hk
  exact ⟨h1, h2, fun u hu hn =>
    W2p_PlanckUnits_planck_system_unique_of_normalizes c G hbar kB hc hG hh hk u hu hn⟩

theorem W2p_PlanckUnits_rationalized_planck_system (c G hbar kB : ℝ) (hc : 0 < c) (hG : 0 < G)
    (hh : 0 < hbar) (hk : 0 < kB)
    (u : UnitSystem) (hu : u.IsPositive) (hn : u.Normalizes c (4 * Real.pi * G) hbar kB) :
    u.length = Real.sqrt (4 * Real.pi * hbar * G / c ^ 3) ∧
    u.mass = Real.sqrt (hbar * c / (4 * Real.pi * G)) ∧
    u.time = Real.sqrt (4 * Real.pi * hbar * G / c ^ 5) ∧
    u.temperature = Real.sqrt (hbar * c ^ 5 / (4 * Real.pi * G)) / kB := by
  rw [W2p_PlanckUnits_planck_system_unique_of_normalizes c (4 * Real.pi * G) hbar kB hc
    (by positivity) hh hk u hu hn]
  simp only [planckSystem]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
    | trivial
    | exact congrArg Real.sqrt (by ring)
    | exact congrArg (fun x => Real.sqrt x / kB) (by ring)

theorem W2p_PlanckUnits_newton_law_nondimensionalized (c G hbar kB : ℝ) (hc : 0 < c)
    (hG : 0 < G) (hh : 0 < hbar)
    (m₁ m₂ r F : ℝ) (hr : 0 < r) :
    F = G * m₁ * m₂ / r ^ 2 ↔
      F / (c ^ 4 / G) =
        (m₁ / (planckSystem c G hbar kB).mass) * (m₂ / (planckSystem c G hbar kB).mass) /
          (r / (planckSystem c G hbar kB).length) ^ 2 := by
  obtain ⟨T, hT0, hTd, hħ, hL, hM, hTe⟩ := W2p_PlanckUnits_repr c G hbar hc hG hh
  have hc0 := hc.ne'
  have hG0 := hG.ne'
  have hT00 := hT0.ne'
  have hr0 := hr.ne'
  simp only [planckSystem]
  rw [hL, hM]
  have e : m₁ / (c ^ 3 * T / G) * (m₂ / (c ^ 3 * T / G)) / (r / (c * T)) ^ 2 =
      (G * m₁ * m₂ / r ^ 2) / (c ^ 4 / G) := by
    field_simp <;> ring
  rw [e, div_left_inj' (by positivity)]

theorem solution (c G hbar kB : ℝ) (hc : 0 < c) (hG : 0 < G)
    (hh : 0 < hbar) (hk : 0 < kB) :
    (planckSystem c G hbar kB).mass * c ^ 2 = Real.sqrt (hbar * c ^ 5 / G) ∧
    (planckSystem c G hbar kB).mass * c = Real.sqrt (hbar * c ^ 3 / G) ∧
    (planckSystem c G hbar kB).mass * c ^ 2 / (planckSystem c G hbar kB).length = c ^ 4 / G ∧
    (planckSystem c G hbar kB).mass / (planckSystem c G hbar kB).length ^ 3 =
      c ^ 5 / (hbar * G ^ 2) ∧
    (planckSystem c G hbar kB).length / (planckSystem c G hbar kB).time ^ 2 =
      Real.sqrt (c ^ 7 / (hbar * G)) ∧
    1 / (planckSystem c G hbar kB).time = Real.sqrt (c ^ 5 / (hbar * G)) ∧
    kB * (planckSystem c G hbar kB).temperature = (planckSystem c G hbar kB).mass * c ^ 2 := by
  obtain ⟨T, hT0, hTd, hħ, hL, hM, hTe⟩ := W2p_PlanckUnits_repr c G hbar hc hG hh
  have hc0 := hc.ne'
  have hG0 := hG.ne'
  have hT00 := hT0.ne'
  have hk0 := hk.ne'
  simp only [planckSystem]
  rw [hTd, hL, hM, hTe, hħ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · field_simp <;> ring
  · symm; apply W2p_PlanckUnits_sqrt_eq _ _ (by positivity); field_simp <;> ring
  · field_simp <;> ring
  · field_simp <;> ring
  · symm; apply W2p_PlanckUnits_sqrt_eq _ _ (by positivity); field_simp <;> ring
  · symm; apply W2p_PlanckUnits_sqrt_eq _ _ (by positivity); field_simp <;> ring
  · field_simp <;> ring

theorem W2p_PlanckUnits_schwarzschild_radius_planck_mass (c G hbar kB : ℝ) (hc : 0 < c)
    (hG : 0 < G) (hh : 0 < hbar) :
    2 * G * (planckSystem c G hbar kB).mass / c ^ 2 =
      2 * (planckSystem c G hbar kB).length := by
  obtain ⟨T, hT0, hTd, hħ, hL, hM, hTe⟩ := W2p_PlanckUnits_repr c G hbar hc hG hh
  have hc0 := hc.ne'
  have hG0 := hG.ne'
  simp only [planckSystem]
  rw [hL, hM]
  field_simp <;> ring

theorem W2p_PlanckUnits_planck_length_eq_reduced_compton (c G hbar kB : ℝ) (hc : 0 < c)
    (hG : 0 < G) (hh : 0 < hbar) :
    hbar / ((planckSystem c G hbar kB).mass * c) = (planckSystem c G hbar kB).length := by
  obtain ⟨T, hT0, hTd, hħ, hL, hM, hTe⟩ := W2p_PlanckUnits_repr c G hbar hc hG hh
  have hc0 := hc.ne'
  have hG0 := hG.ne'
  have hT00 := hT0.ne'
  simp only [planckSystem]
  rw [hL, hM, hħ]
  field_simp <;> ring

theorem W2p_PlanckUnits_planck_length_eq_c_mul_planck_time (c G hbar kB : ℝ) (hc : 0 < c)
    (hG : 0 < G) (hh : 0 < hbar) :
    (planckSystem c G hbar kB).length = c * (planckSystem c G hbar kB).time := by
  obtain ⟨T, hT0, hTd, hħ, hL, hM, hTe⟩ := W2p_PlanckUnits_repr c G hbar hc hG hh
  simp only [planckSystem]
  rw [hTd, hL]
