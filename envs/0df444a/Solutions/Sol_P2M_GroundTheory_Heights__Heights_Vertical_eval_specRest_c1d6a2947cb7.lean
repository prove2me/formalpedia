-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_eval_specRest_c1d6a2947cb7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:43.537547+00:00
-- url     : https://prove2.me/submissions/29c99147-f829-4bb2-bc96-17107b5e6b25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSpecFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecLinNZD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {k E : Type*} [CommRing k] [CommRing E] (φ : k →+* E) {n e : ℕ}
    (g : MvPolynomial (Fin (e + 1) × Fin n) k) (y : Par e n → E) (u : Fin n → k) :
    eval (fun j => φ (u j)) (specRest φ g y) =
      eval₂ φ (fun ij : Fin e × Fin n => y (.inl ij)) (specFirst g u) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [specRest, specFirst]
  | add p q hp hq =>
    simp only [specRest, specFirst, eval₂_add, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p ij hp =>
    simp only [specRest, specFirst, eval₂_mul, eval₂_X, map_mul, bind₁_X_right] at hp ⊢
    rw [hp]
    congr 1
    obtain ⟨i, j⟩ := ij
    cases i using Fin.cases <;> simp [specFirstVar]
end GroundTheory.Heights₂.Heights.Vertical
