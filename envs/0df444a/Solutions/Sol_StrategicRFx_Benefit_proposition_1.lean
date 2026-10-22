-- Prove2me | solution 1 for StrategicRFx.Benefit.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T02:17:50.8579+00:00
-- url     : https://prove2.me/submissions/088b3fb1-c8f0-45c8-9a39-7576932d3e02

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Setting

open StrategicRFx.Benefit

lemma rfx5_Qbound (θ0 θ1 a0 a1 x0 x1 F0 F1 : ℝ) (h0 : 0 < θ0) (h0' : θ0 < 1) (h1 : 0 < θ1)
    (h1' : θ1 < 1) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hF0 : F0 = θ0 * max (a0 - F1) 0) (hF1 : F1 = θ1 * max (a1 - F0) 0)
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1)
    (hq0 : x0 ≤ θ0 * max (a0 - x1) 0) (hq1 : x1 ≤ θ1 * max (a1 - x0) 0) :
    x0 + x1 ≤ F0 + F1 := by
  have h01 : 0 < 1 - θ0 * θ1 := by nlinarith
  rcases le_total 0 (a0 - F1) with hA | hA <;>
  rcases le_total 0 (a1 - F0) with hB | hB <;>
  rcases le_total 0 (a0 - x1) with hC | hC <;>
  rcases le_total 0 (a1 - x0) with hD | hD <;>
  simp only [max_eq_left hA, max_eq_right hA, max_eq_left hB, max_eq_right hB,
    max_eq_left hC, max_eq_right hC, max_eq_left hD, max_eq_right hD, mul_zero] at hF0 hF1 hq0 hq1 <;>
  nlinarith [mul_le_mul_of_nonneg_left hq0 (by linarith : (0:ℝ) ≤ 1 - θ1),
    mul_le_mul_of_nonneg_left hq1 (by linarith : (0:ℝ) ≤ 1 - θ0),
    mul_pos h0 h1, mul_pos h0 ha0, mul_pos h1 ha1, mul_pos (by linarith : (0:ℝ) < 1 - θ1) h0,
    mul_pos (by linarith : (0:ℝ) < 1 - θ0) h1]

lemma rfx5_Sbound (θ0 θ1 a0 a1 y0 y1 F0 F1 : ℝ) (h0 : 0 < θ0) (h0' : θ0 < 1) (h1 : 0 < θ1)
    (h1' : θ1 < 1) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hF0 : F0 = θ0 * max (a0 - F1) 0) (hF1 : F1 = θ1 * max (a1 - F0) 0)
    (hy0 : 0 ≤ y0) (hy1 : 0 ≤ y1)
    (hq0 : θ0 * max (a0 - y1) 0 ≤ y0) (hq1 : θ1 * max (a1 - y0) 0 ≤ y1) :
    F0 + F1 ≤ y0 + y1 := by
  have h01 : 0 < 1 - θ0 * θ1 := by nlinarith
  rcases le_total 0 (a0 - F1) with hA | hA <;>
  rcases le_total 0 (a1 - F0) with hB | hB <;>
  rcases le_total 0 (a0 - y1) with hC | hC <;>
  rcases le_total 0 (a1 - y0) with hD | hD <;>
  simp only [max_eq_left hA, max_eq_right hA, max_eq_left hB, max_eq_right hB,
    max_eq_left hC, max_eq_right hC, max_eq_left hD, max_eq_right hD, mul_zero] at hF0 hF1 hq0 hq1 <;>
  nlinarith [mul_le_mul_of_nonneg_left hq0 (by linarith : (0:ℝ) ≤ 1 - θ1),
    mul_le_mul_of_nonneg_left hq1 (by linarith : (0:ℝ) ≤ 1 - θ0),
    mul_pos h0 h1, mul_pos h0 ha0, mul_pos h1 ha1, mul_pos (by linarith : (0:ℝ) < 1 - θ1) h0,
    mul_pos (by linarith : (0:ℝ) < 1 - θ0) h1]

lemma rfx5_follower (θ A x : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hx0 : 0 ≤ x) (hxA : x ≤ A)
    (hmax : ∀ y, 0 ≤ y → y ≤ A → nashProduct θ y (A - y) ≤ nashProduct θ x (A - x)) :
    θ * A ≤ x := by
  by_contra hlt
  push_neg at hlt
  have hA : 0 < A := by nlinarith
  have hθA : 0 < θ * A := mul_pos hθ0 hA
  have h1θ : 0 < 1 - θ := by linarith
  have h1θA : 0 < (1 - θ) * A := mul_pos h1θ hA
  set p1 := x / (θ * A) with hp1
  set p2 := (A - x) / ((1 - θ) * A) with hp2
  have hp1n : 0 ≤ p1 := div_nonneg hx0 hθA.le
  have hp2n : 0 ≤ p2 := div_nonneg (by linarith) h1θA.le
  have hne : p1 ≠ p2 := by
    intro h
    rw [hp1, hp2, div_eq_div_iff hθA.ne' h1θA.ne'] at h
    have : (x - θ * A) * A = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith
  have hlt' := (Real.geom_mean_lt_arith_mean2_weighted_iff_of_pos hθ0 h1θ hp1n hp2n
    (by ring)).2 hne
  have hsum : θ * p1 + (1 - θ) * p2 = 1 := by
    rw [hp1, hp2]; field_simp; ring
  have ex : x = p1 * (θ * A) := by rw [hp1]; field_simp
  have eAx : A - x = p2 * ((1 - θ) * A) := by rw [hp2]; field_simp
  have key : nashProduct θ x (A - x) =
      (p1 ^ θ * p2 ^ (1 - θ)) * nashProduct θ (θ * A) (A - θ * A) := by
    unfold nashProduct
    rw [show A - θ * A = (1 - θ) * A by ring]
    rw [eAx]
    conv_lhs => rw [ex]
    rw [Real.mul_rpow hp1n hθA.le, Real.mul_rpow hp2n h1θA.le]
    ring
  have hpos : 0 < nashProduct θ (θ * A) (A - θ * A) := by
    unfold nashProduct
    rw [show A - θ * A = (1 - θ) * A by ring]
    exact mul_pos (Real.rpow_pos_of_pos hθA _) (Real.rpow_pos_of_pos h1θA _)
  have hm := hmax (θ * A) hθA.le (by nlinarith)
  rw [key] at hm
  nlinarith

set_option maxHeartbeats 4000000 in
lemma rfx5_Quniq (θ0 θ1 a0 a1 x0 x1 F0 F1 : ℝ) (h0 : 0 < θ0) (h0' : θ0 < 1) (h1 : 0 < θ1)
    (h1' : θ1 < 1) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hF0 : F0 = θ0 * max (a0 - F1) 0) (hF1 : F1 = θ1 * max (a1 - F0) 0)
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1)
    (hq0 : x0 ≤ θ0 * max (a0 - x1) 0) (hq1 : x1 ≤ θ1 * max (a1 - x0) 0)
    (hs : x0 + x1 = F0 + F1) : x0 = F0 ∧ x1 = F1 := by
  have h01 : 0 < 1 - θ0 * θ1 := by nlinarith
  rcases le_total 0 (a0 - F1) with hA | hA <;>
  rcases le_total 0 (a1 - F0) with hB | hB <;>
  rcases le_total 0 (a0 - x1) with hC | hC <;>
  rcases le_total 0 (a1 - x0) with hD | hD <;>
  simp only [max_eq_left hA, max_eq_right hA, max_eq_left hB, max_eq_right hB,
    max_eq_left hC, max_eq_right hC, max_eq_left hD, max_eq_right hD, mul_zero] at hF0 hF1 hq0 hq1 <;>
  constructor <;>
  nlinarith [mul_le_mul_of_nonneg_left hq0 (by linarith : (0:ℝ) ≤ 1 - θ1),
    mul_le_mul_of_nonneg_left hq1 (by linarith : (0:ℝ) ≤ 1 - θ0),
    mul_pos h0 h1, mul_pos h0 ha0, mul_pos h1 ha1, mul_pos (by linarith : (0:ℝ) < 1 - θ1) h0,
    mul_pos (by linarith : (0:ℝ) < 1 - θ0) h1]


lemma rfx5_follower_max (θ A y : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hA0 : 0 ≤ A) (hy0 : 0 ≤ y)
    (hyA : y ≤ A) : nashProduct θ y (A - y) ≤ nashProduct θ (θ * A) (A - θ * A) := by
  rcases eq_or_lt_of_le hA0 with hA | hA
  · subst hA
    have : y = 0 := le_antisymm hyA hy0
    subst this
    simp
  have hθA : 0 < θ * A := mul_pos hθ0 hA
  have h1θ : 0 < 1 - θ := by linarith
  have h1θA : 0 < (1 - θ) * A := mul_pos h1θ hA
  set p1 := y / (θ * A) with hp1
  set p2 := (A - y) / ((1 - θ) * A) with hp2
  have hp1n : 0 ≤ p1 := div_nonneg hy0 hθA.le
  have hp2n : 0 ≤ p2 := div_nonneg (by linarith) h1θA.le
  have hle := Real.geom_mean_le_arith_mean2_weighted hθ0.le h1θ.le hp1n hp2n (by ring)
  have hsum : θ * p1 + (1 - θ) * p2 = 1 := by
    rw [hp1, hp2]; field_simp; ring
  have ex : y = p1 * (θ * A) := by rw [hp1]; field_simp
  have eAx : A - y = p2 * ((1 - θ) * A) := by rw [hp2]; field_simp
  have key : nashProduct θ y (A - y) =
      (p1 ^ θ * p2 ^ (1 - θ)) * nashProduct θ (θ * A) (A - θ * A) := by
    unfold nashProduct
    rw [show A - θ * A = (1 - θ) * A by ring]
    rw [eAx]
    conv_lhs => rw [ex]
    rw [Real.mul_rpow hp1n hθA.le, Real.mul_rpow hp2n h1θA.le]
    ring
  have hpos : 0 < nashProduct θ (θ * A) (A - θ * A) := by
    unfold nashProduct
    rw [show A - θ * A = (1 - θ) * A by ring]
    exact mul_pos (Real.rpow_pos_of_pos hθA _) (Real.rpow_pos_of_pos h1θA _)
  rw [key]
  nlinarith

lemma rfx5_fix_exists (θ0 θ1 a0 a1 : ℝ) (h0 : 0 < θ0) (h0' : θ0 < 1) (h1 : 0 < θ1)
    (h1' : θ1 < 1) (ha0 : 0 < a0) (ha1 : 0 < a1) :
    ∃ F0 F1 : ℝ, F0 = θ0 * max (a0 - F1) 0 ∧ F1 = θ1 * max (a1 - F0) 0 := by
  by_cases c1 : a0 ≤ θ1 * a1
  · refine ⟨0, θ1 * a1, ?_, ?_⟩
    · rw [max_eq_right (by linarith)]; ring
    · rw [sub_zero, max_eq_left ha1.le]
  by_cases c2 : a1 ≤ θ0 * a0
  · refine ⟨θ0 * a0, 0, ?_, ?_⟩
    · rw [sub_zero, max_eq_left ha0.le]
    · rw [max_eq_right (by linarith)]; ring
  push_neg at c1 c2
  have hd : 0 < 1 - θ0 * θ1 := by nlinarith
  refine ⟨θ0 * ((a0 - θ1 * a1) / (1 - θ0 * θ1)), θ1 * ((a1 - θ0 * a0) / (1 - θ0 * θ1)), ?_, ?_⟩
  · have e : a0 - θ1 * ((a1 - θ0 * a0) / (1 - θ0 * θ1)) = (a0 - θ1 * a1) / (1 - θ0 * θ1) := by
      rw [eq_div_iff hd.ne', sub_mul, mul_assoc, div_mul_cancel₀ _ hd.ne']; ring
    rw [e, max_eq_left (div_nonneg (by linarith) hd.le)]
  · have e : a1 - θ0 * ((a0 - θ1 * a1) / (1 - θ0 * θ1)) = (a1 - θ0 * a0) / (1 - θ0 * θ1) := by
      rw [eq_div_iff hd.ne', sub_mul, mul_assoc, div_mul_cancel₀ _ hd.ne']; ring
    rw [e, max_eq_left (div_nonneg (by linarith) hd.le)]

lemma rfx5_other_other (i : Fin 2) : other (other i) = i := by
  fin_cases i <;> decide

theorem solution (P : Params) (hP : Standing P) :
    (∃! πF : Fin 2 → ℝ, ∀ i, πF i = P.θ i * max (P.Pi - πF (other i) - P.PiEx i) 0) ∧
    ∀ πF : Fin 2 → ℝ, (∀ i, πF i = P.θ i * max (P.Pi - πF (other i) - P.PiEx i) 0) →
      IsGreatest {v : ℝ | ∃ π πex : Fin 2 → ℝ, IsSimuEquilibrium P π πex ∧ v = P.Pi - π 0 - π 1}
        (P.Pi - πF 0 - πF 1) := by
  have o0 : other 0 = 1 := by decide
  have o1 : other 1 = 0 := by decide
  have ha0 : 0 < P.Pi - P.PiEx 0 := by linarith [hP.PiEx_lt 0]
  have ha1 : 0 < P.Pi - P.PiEx 1 := by linarith [hP.PiEx_lt 1]
  -- normal form of the fixed-point equations
  have norm : ∀ F : Fin 2 → ℝ, (∀ i, F i = P.θ i * max (P.Pi - F (other i) - P.PiEx i) 0) ↔
      (F 0 = P.θ 0 * max ((P.Pi - P.PiEx 0) - F 1) 0 ∧
        F 1 = P.θ 1 * max ((P.Pi - P.PiEx 1) - F 0) 0) := by
    intro F
    constructor
    · intro h
      have h0 := h 0
      have h1 := h 1
      rw [o0, show P.Pi - F 1 - P.PiEx 0 = (P.Pi - P.PiEx 0) - F 1 by ring] at h0
      rw [o1, show P.Pi - F 0 - P.PiEx 1 = (P.Pi - P.PiEx 1) - F 0 by ring] at h1
      exact ⟨h0, h1⟩
    · rintro ⟨h0, h1⟩ i
      fin_cases i
      · show F 0 = P.θ 0 * max (P.Pi - F (other 0) - P.PiEx 0) 0
        rw [o0, show P.Pi - F 1 - P.PiEx 0 = (P.Pi - P.PiEx 0) - F 1 by ring]; exact h0
      · show F 1 = P.θ 1 * max (P.Pi - F (other 1) - P.PiEx 1) 0
        rw [o1, show P.Pi - F 0 - P.PiEx 1 = (P.Pi - P.PiEx 1) - F 0 by ring]; exact h1
  have hθ0 := hP.θ_pos 0
  have hθ1 := hP.θ_pos 1
  have hθ0' := hP.θ_lt_one 0
  have hθ1' := hP.θ_lt_one 1
  have nn : ∀ F : Fin 2 → ℝ, (∀ i, F i = P.θ i * max (P.Pi - F (other i) - P.PiEx i) 0) →
      ∀ i, 0 ≤ F i := by
    intro F hF i; rw [hF i]; exact mul_nonneg (hP.θ_pos i).le (le_max_right _ _)
  refine ⟨?_, ?_⟩
  · obtain ⟨F0, F1, e0, e1⟩ := rfx5_fix_exists (P.θ 0) (P.θ 1) _ _ hθ0 hθ0' hθ1 hθ1' ha0 ha1
    refine ⟨![F0, F1], (norm _).2 ⟨by simpa using e0, by simpa using e1⟩, ?_⟩
    intro G hG
    have hGn := nn G hG
    have hFn := nn ![F0, F1] ((norm _).2 ⟨by simpa using e0, by simpa using e1⟩)
    obtain ⟨g0, g1⟩ := (norm G).1 hG
    have b1 := rfx5_Qbound (P.θ 0) (P.θ 1) _ _ (G 0) (G 1) F0 F1 hθ0 hθ0' hθ1 hθ1' ha0 ha1
      e0 e1 (hGn 0) (hGn 1) g0.le g1.le
    have b2 := rfx5_Qbound (P.θ 0) (P.θ 1) _ _ F0 F1 (G 0) (G 1) hθ0 hθ0' hθ1 hθ1' ha0 ha1
      g0 g1 (by simpa using hFn 0) (by simpa using hFn 1) e0.le e1.le
    obtain ⟨u0, u1⟩ := rfx5_Quniq (P.θ 0) (P.θ 1) _ _ (G 0) (G 1) F0 F1 hθ0 hθ0' hθ1 hθ1'
      ha0 ha1 e0 e1 (hGn 0) (hGn 1) g0.le g1.le (by linarith)
    funext i
    fin_cases i
    · simpa using u0
    · simpa using u1
  intro πF hF
  obtain ⟨hF0, hF1⟩ := (norm πF).1 hF
  refine ⟨?_, ?_⟩
  · -- πF is attained by an equilibrium
    refine ⟨πF, fun j => max (πF j - (P.Pi - P.PiEx (other j))) 0, ⟨fun j => le_max_right _ _,
      fun i => ?_⟩, rfl⟩
    show IsFollowerSolution P i (πF (other i))
      (P.PiEx i - max (πF (other i) - (P.Pi - P.PiEx (other (other i)))) 0) (πF i)
    rw [rfx5_other_other]
    set A := max (P.Pi - P.PiEx i - πF (other i)) 0 with hAdef
    have hA0 : 0 ≤ A := le_max_right _ _
    have hAe : P.Pi - πF (other i) - (P.PiEx i - max (πF (other i) - (P.Pi - P.PiEx i)) 0) = A := by
      rw [hAdef]
      rcases le_total 0 (P.Pi - P.PiEx i - πF (other i)) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    have hFi : πF i = P.θ i * A := by
      rw [hF i, hAdef, show P.Pi - πF (other i) - P.PiEx i = P.Pi - P.PiEx i - πF (other i) by ring]
    have e : ∀ z, P.Pi - πF (other i) - z - (P.PiEx i - max (πF (other i) - (P.Pi - P.PiEx i)) 0)
        = A - z := fun z => by rw [← hAe]; ring
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hFi]; exact mul_nonneg (hP.θ_pos i).le hA0
    · have : P.θ i * A ≤ A := by nlinarith [hP.θ_lt_one i]
      linarith
    · intro y hy
      obtain ⟨hy0, hyA⟩ := hy
      rw [e, e, hFi]
      exact rfx5_follower_max (P.θ i) A y (hP.θ_pos i) (hP.θ_lt_one i) hA0 hy0 (by linarith)
  · -- upper bound over all equilibria
    rintro v ⟨π, πex, he, rfl⟩
    have hS : ∀ i, 0 ≤ π i ∧ P.θ i * max (P.Pi - π (other i) - P.PiEx i) 0 ≤ π i := by
      intro i
      obtain ⟨⟨hx0, hxA⟩, hmax⟩ := he.2 i
      set A := P.Pi - π (other i) - (P.PiEx i - πex (other i)) with hA
      have key : P.θ i * A ≤ π i := by
        apply rfx5_follower (P.θ i) A (π i) (hP.θ_pos i) (hP.θ_lt_one i) hx0 (by linarith)
        intro y hy0 hyA
        have e : ∀ z, P.Pi - π (other i) - z - (P.PiEx i - πex (other i)) = A - z := fun z => by
          rw [hA]; ring
        have := hmax y ⟨hy0, by linarith⟩
        rw [e, e] at this
        exact this
      refine ⟨hx0, ?_⟩
      have hex := he.1 (other i)
      have hA0 : 0 ≤ A := by linarith
      have : max (P.Pi - π (other i) - P.PiEx i) 0 ≤ A := max_le (by linarith) hA0
      exact (mul_le_mul_of_nonneg_left this (hP.θ_pos i).le).trans key
    obtain ⟨hy0, hs0⟩ := hS 0
    obtain ⟨hy1, hs1⟩ := hS 1
    rw [o0, show P.Pi - π 1 - P.PiEx 0 = (P.Pi - P.PiEx 0) - π 1 by ring] at hs0
    rw [o1, show P.Pi - π 0 - P.PiEx 1 = (P.Pi - P.PiEx 1) - π 0 by ring] at hs1
    have h2 := rfx5_Sbound (P.θ 0) (P.θ 1) _ _ (π 0) (π 1) (πF 0) (πF 1) hθ0 hθ0' hθ1 hθ1'
      ha0 ha1 hF0 hF1 hy0 hy1 hs0 hs1
    show P.Pi - π 0 - π 1 ≤ P.Pi - πF 0 - πF 1
    linarith
