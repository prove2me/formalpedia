-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Norm.eval_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:26:06.611949+00:00
-- url     : https://prove2.me/submissions/e6387a9f-40d8-4171-b0fe-a2bf660da9df

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_HoloSectionStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_LineFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Norm
open Filter Topology Asymptotics
universe u
namespace ReciprocityTheory.L2DbarEstimates.Norm
theorem _root_.solution (n : ℕ) (Δ : MvPolynomial (Fin n) ℂ) (w : V n) (t : ℂ) :
    (MvPolynomial.aeval (fun i => Polynomial.C (w i) * Polynomial.X) Δ).eval t =
      polyAt n Δ (t • w) := by
  unfold polyAt
  induction Δ using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.eval_mul, hp, MvPolynomial.eval_mul, MvPolynomial.aeval_X,
      MvPolynomial.eval_X]
    congr 1
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    simp
    ring
end ReciprocityTheory.L2DbarEstimates.Norm
