-- Prove2me | solution 1 for ServiceParts.RealTime.G_convex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T14:58:29.148514+00:00
-- url     : https://prove2.me/submissions/2b4a7add-faf4-45d9-9780-2a4b9645dccc

import Mathlib
import Definitions.Def_ServiceParts_RealTime_Model

open MeasureTheory

set_option autoImplicit false

namespace ServiceParts.RealTime.G_convex_aux

theorem term_ineq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → ℕ) (hX : Integrable (fun ω => (X ω : ℝ)) P) (S : ℤ) :
    (∫ ω, max (((S + 1 : ℤ) : ℝ) - (X ω : ℝ)) 0 ∂P) - ∫ ω, max ((S : ℝ) - (X ω : ℝ)) 0 ∂P ≤
      (∫ ω, max (((S + 2 : ℤ) : ℝ) - (X ω : ℝ)) 0 ∂P)
        - ∫ ω, max (((S + 1 : ℤ) : ℝ) - (X ω : ℝ)) 0 ∂P := by
  have hI : ∀ c : ℝ, Integrable (fun ω => max (c - (X ω : ℝ)) 0) P := fun c =>
    ((integrable_const c).sub hX).pos_part
  have key : (∫ ω, (max (((S + 1 : ℤ) : ℝ) - (X ω : ℝ)) 0
        + max (((S + 1 : ℤ) : ℝ) - (X ω : ℝ)) 0) ∂P) ≤
      ∫ ω, (max ((S : ℝ) - (X ω : ℝ)) 0 + max (((S + 2 : ℤ) : ℝ) - (X ω : ℝ)) 0) ∂P := by
    apply integral_mono ((hI _).add (hI _)) ((hI _).add (hI _))
    intro ω
    simp only [Pi.add_apply]
    push_cast
    have a1 := le_max_left ((S : ℝ) - (X ω : ℝ)) 0
    have a2 := le_max_right ((S : ℝ) - (X ω : ℝ)) 0
    have a3 := le_max_left ((S : ℝ) + 2 - (X ω : ℝ)) 0
    have a4 := le_max_right ((S : ℝ) + 2 - (X ω : ℝ)) 0
    rcases max_cases ((S : ℝ) + 1 - (X ω : ℝ)) 0 with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> linarith
  rw [integral_add (hI _) (hI _), integral_add (hI _) (hI _)] at key
  linarith

theorem term_ineq' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → ℕ) (hX : Integrable (fun ω => (X ω : ℝ)) P) (S : ℤ) :
    (∫ ω, max ((X ω : ℝ) - ((S + 1 : ℤ) : ℝ)) 0 ∂P) - ∫ ω, max ((X ω : ℝ) - (S : ℝ)) 0 ∂P ≤
      (∫ ω, max ((X ω : ℝ) - ((S + 2 : ℤ) : ℝ)) 0 ∂P)
        - ∫ ω, max ((X ω : ℝ) - ((S + 1 : ℤ) : ℝ)) 0 ∂P := by
  have hI : ∀ c : ℝ, Integrable (fun ω => max ((X ω : ℝ) - c) 0) P := fun c =>
    (hX.sub (integrable_const c)).pos_part
  have key : (∫ ω, (max ((X ω : ℝ) - ((S + 1 : ℤ) : ℝ)) 0
        + max ((X ω : ℝ) - ((S + 1 : ℤ) : ℝ)) 0) ∂P) ≤
      ∫ ω, (max ((X ω : ℝ) - (S : ℝ)) 0 + max ((X ω : ℝ) - ((S + 2 : ℤ) : ℝ)) 0) ∂P := by
    apply integral_mono ((hI _).add (hI _)) ((hI _).add (hI _))
    intro ω
    simp only [Pi.add_apply]
    push_cast
    have a1 := le_max_left ((X ω : ℝ) - (S : ℝ)) 0
    have a2 := le_max_right ((X ω : ℝ) - (S : ℝ)) 0
    have a3 := le_max_left ((X ω : ℝ) - ((S : ℝ) + 2)) 0
    have a4 := le_max_right ((X ω : ℝ) - ((S : ℝ) + 2)) 0
    rcases max_cases ((X ω : ℝ) - ((S : ℝ) + 1)) 0 with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> linarith
  rw [integral_add (hI _) (hI _), integral_add (hI _) (hI _)] at key
  linarith

end ServiceParts.RealTime.G_convex_aux

open MeasureTheory ServiceParts.RealTime in
theorem solution {J : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ItemModel J Ω P) (j : J) (t : ℕ) :
    DiscreteConvex (M.G j t) := by
  intro S
  unfold ItemModel.G
  have h1 := ServiceParts.RealTime.G_convex_aux.term_ineq _ (M.X_integrable j t) S
  have h2 := ServiceParts.RealTime.G_convex_aux.term_ineq' _ (M.X_integrable j t) S
  have hh := mul_le_mul_of_nonneg_left h1 (M.h_pos j).le
  have hb := mul_le_mul_of_nonneg_left h2 (M.b_pos j).le
  rw [mul_sub, mul_sub] at hh hb
  push_cast at hh hb ⊢
  linarith
