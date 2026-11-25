-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_not_isChowForm_zero_1689bf6b18f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:40:55.326353+00:00
-- url     : https://prove2.me/submissions/5f1d1d66-16d0-481f-86a8-cd9223a154af

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PCharacterised

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
theorem _root_.solution (hPt : ProjPrimeHasPoint.Statement) {F : Type} [Field F] {n : ℕ}
    {W : Ideal (MvPolynomial (Fin n) F)} (hW : IsProjPrime W) (g : MvPolynomial (Fin 0 × Fin n) F) :
    ¬ IsChowForm W 0 g := by
  intro hg
  obtain ⟨x, hx, hxW⟩ := hPt F n W hW
  have hunit : g ∣ 1 := by
    rw [eq_C_of_isEmpty g] at hg ⊢
    have hc : coeff 0 g ≠ 0 := fun h => hg.1 (by rw [h, map_zero])
    exact ⟨C (coeff 0 g)⁻¹, by rw [← C_mul, mul_inv_cancel₀ hc, C_1]⟩
  have hinc : (fun _ => 0 : Fin 0 × Fin n → AlgebraicClosure F) ∈ incidence W 0 :=
    ⟨x, hx, hxW, fun i => i.elim0⟩
  have := (hg.2 1).mpr hunit _ hinc
  simp at this
end GroundTheory.Heights₂.Heights
