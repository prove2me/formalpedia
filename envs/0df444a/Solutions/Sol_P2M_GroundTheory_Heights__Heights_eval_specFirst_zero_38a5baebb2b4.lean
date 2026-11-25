-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_eval_specFirst_zero_38a5baebb2b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:47:46.899902+00:00
-- url     : https://prove2.me/submissions/20198837-79d9-4805-9648-c5b36a787a86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PMahlerZeroSpec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open MeasureTheory MvPolynomial
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (f : MvPolynomial (Fin 1 × Fin n) ℂ) (u : Fin n → ℂ)
    (v : Fin 0 × Fin n → ℂ) : eval v (specFirst f u) = eval (fun ij => u ij.2) f := by
  unfold specFirst
  show eval₂Hom (RingHom.id ℂ) v (bind₁ (specFirstVar u) f) = eval₂Hom (RingHom.id ℂ) _ f
  rw [eval₂Hom_bind₁]
  congr 2
  funext ij
  obtain ⟨i, j⟩ := ij
  obtain rfl : i = 0 := Fin.fin_one_eq_zero i
  simp [specFirstVar]
end GroundTheory.Heights₂.Heights
