-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_incidence_point_247b5a18c1c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:38:36.993354+00:00
-- url     : https://prove2.me/submissions/12fd6361-d9cb-4392-9912-f318a77ff4f7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {F : Type*} [Field F] (u : Fin 1 × Fin 1 → AlgebraicClosure F) :
    u ∈ incidence (⊥ : Ideal (MvPolynomial (Fin 1) F)) 1 ↔ u = 0 := by
  constructor
  · rintro ⟨x, hx, -, hu⟩
    have hx0 : x 0 ≠ 0 := fun h => hx (funext fun j => by rw [Fin.fin_one_eq_zero j]; exact h)
    have h := hu 0
    simp only [Fin.sum_univ_one] at h
    have hu0 : u (0, 0) = 0 := (mul_eq_zero.mp h).resolve_right hx0
    funext ij
    obtain rfl : ij = (0, 0) := Subsingleton.elim _ _
    exact hu0
  · rintro rfl
    refine ⟨fun _ => 1, fun h => one_ne_zero (congrFun h 0), fun g hg => ?_, fun i => ?_⟩
    · rw [Ideal.mem_bot] at hg
      simp [hg]
    · simp
end GroundTheory.Heights₂.Heights
