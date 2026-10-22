-- Prove2me | solution 1 for RelationalReciprocity.Dynamics.bonus_formula
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:36:57.757048+00:00
-- url     : https://prove2.me/submissions/f2f8c504-484b-4af0-8461-5b856bb1e725

import Mathlib
import Definitions.Def_RelationalReciprocity_Dynamics_Model
set_option autoImplicit false

open RelationalReciprocity.Dynamics

theorem solution (P : Params) (hP : P.Standing) (hη : 0 < P.η) :
    (∀ lam : ℝ, 0 ≤ lam → 1 < P.η ^ 2 * P.θ ^ 3 * (1 + lam) →
      bonus P (kktEffort P lam) (kktWage P lam) =
        (3 * P.η ^ 2 * P.θ ^ 3 * (1 + lam) - 1) / (6 * P.η ^ 3 * P.θ ^ 3 * (1 + lam) ^ 3)) ∧
    (∀ lam : ℝ, 0 ≤ lam → bonus P (kktEffort0 P lam) 0 = kktEffort0 P lam ^ 3 / 3) ∧
    StrictAntiOn (fun lam => bonus P (kktEffort P lam) (kktWage P lam))
      {lam : ℝ | 0 ≤ lam ∧ 1 < P.η ^ 2 * P.θ ^ 3 * (1 + lam)} ∧
    StrictAntiOn (fun lam => bonus P (kktEffort0 P lam) 0) (Set.Ici 0) := by
  obtain ⟨hθ, -, -, -, -⟩ := hP
  have hP1 : ∀ lam : ℝ, 0 ≤ lam → 1 < P.η ^ 2 * P.θ ^ 3 * (1 + lam) →
      bonus P (kktEffort P lam) (kktWage P lam) =
        (3 * P.η ^ 2 * P.θ ^ 3 * (1 + lam) - 1) / (6 * P.η ^ 3 * P.θ ^ 3 * (1 + lam) ^ 3) := by
    intro lam hl h1
    have hl1 : 0 < 1 + lam := by linarith
    have hs : Real.sqrt (P.η * kktWage P lam * P.θ)
        = (P.η ^ 2 * P.θ ^ 3 * (1 + lam) - 1) / (2 * P.η * P.θ * (1 + lam)) := by
      have : P.η * kktWage P lam * P.θ
          = ((P.η ^ 2 * P.θ ^ 3 * (1 + lam) - 1) / (2 * P.η * P.θ * (1 + lam))) ^ 2 := by
        unfold kktWage
        field_simp
        ring
      rw [this]
      apply Real.sqrt_sq
      apply div_nonneg (by linarith) (by positivity)
    unfold bonus
    rw [hs]
    unfold kktEffort kktWage
    field_simp
    ring
  have hP2 : ∀ lam : ℝ, 0 ≤ lam → bonus P (kktEffort0 P lam) 0 = kktEffort0 P lam ^ 3 / 3 := by
    intro lam _
    unfold bonus
    simp
  refine ⟨hP1, hP2, ?_, ?_⟩
  · intro a ha b hb hab
    simp only
    rw [hP1 a ha.1 ha.2, hP1 b hb.1 hb.2]
    have hA : 0 < P.η ^ 2 * P.θ ^ 3 := by positivity
    have hC : 0 < 6 * P.η ^ 3 * P.θ ^ 3 := by positivity
    set A := P.η ^ 2 * P.θ ^ 3 with hAdef
    have e1 : 3 * P.η ^ 2 * P.θ ^ 3 * (1 + b) - 1 = 3 * A * (1 + b) - 1 := by rw [hAdef]; ring
    have e2 : 3 * P.η ^ 2 * P.θ ^ 3 * (1 + a) - 1 = 3 * A * (1 + a) - 1 := by rw [hAdef]; ring
    rw [e1, e2]
    have ha1 : 1 < A * (1 + a) := ha.2
    have hb1 : 1 < A * (1 + b) := hb.2
    have hs1 : 0 < 1 + a := by have := ha.1; linarith
    have hs2 : 0 < 1 + b := by have := hb.1; linarith
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have hab' : 1 + a < 1 + b := by linarith
    set s1 := 1 + a with hs1def
    set s2 := 1 + b with hs2def
    have t0 : 0 < s2 * (s1 + s2) := by positivity
    have t1 : 3 * s2 * (s1 + s2) < 3 * (A * s1) * s2 * (s1 + s2) := by nlinarith
    have t2 : 0 < 3 * A * s1 * s2 * (s1 + s2) - (s1 ^ 2 + s1 * s2 + s2 ^ 2) := by nlinarith [mul_pos hs1 hs2]
    have key : (3 * A * s2 - 1) * s1 ^ 3 < (3 * A * s1 - 1) * s2 ^ 3 := by
      have := mul_pos (sub_pos.mpr hab') t2
      nlinarith
    have := mul_lt_mul_of_pos_left key hC
    nlinarith
  · intro a ha b hb hab
    simp only
    rw [hP2 a ha, hP2 b hb]
    have ha' : 0 < 1 + a := by have := Set.mem_Ici.mp ha; linarith
    have h1 : P.θ / (1 + b) < P.θ / (1 + a) := div_lt_div_of_pos_left hθ ha' (by linarith)
    have h2 : kktEffort0 P b < kktEffort0 P a := Real.sqrt_lt_sqrt (div_pos hθ (by have := Set.mem_Ici.mp hb; linarith)).le h1
    have h3 : 0 ≤ kktEffort0 P b := Real.sqrt_nonneg _
    have := pow_lt_pow_left₀ h2 h3 (by norm_num : (3:ℕ) ≠ 0)
    linarith
