-- Prove2me | solution 1 for ServiceParts.RealTime.Q_convex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T14:42:11.360303+00:00
-- url     : https://prove2.me/submissions/6ad51c78-9bd9-4ce5-bcdb-f930ddcb606e

import Mathlib
import Definitions.Def_ServiceParts_RealTime_Model

open MeasureTheory

set_option autoImplicit false

namespace ServiceParts.RealTime.Q_convex_aux

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

end ServiceParts.RealTime.Q_convex_aux

open MeasureTheory ServiceParts.RealTime in
theorem solution {J : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ItemModel J Ω P) (j : J) :
    DiscreteConvex (M.Q j) := by
  intro S
  unfold ItemModel.Q
  have hs := fun S : ℤ => M.Q_summable j S
  rw [← mul_sub, ← mul_sub, ← (hs _).tsum_sub (hs _), ← (hs _).tsum_sub (hs _)]
  apply mul_le_mul_of_nonneg_left _ (M.h_pos j).le
  apply Summable.tsum_le_tsum _ ((hs _).sub (hs _)) ((hs _).sub (hs _))
  intro n
  exact ServiceParts.RealTime.Q_convex_aux.term_ineq _ (M.X_integrable j _) S
