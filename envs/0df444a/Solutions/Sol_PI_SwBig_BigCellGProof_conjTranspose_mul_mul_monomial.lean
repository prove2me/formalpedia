-- Prove2me | solution 1 for PI.SwBig.BigCellGProof.conjTranspose_mul_mul_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:06.775376+00:00
-- url     : https://prove2.me/submissions/44ec3226-8997-4d18-830d-7fec37de974a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BigCellConjugation_Monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SwBig PI.SwBig.BigCellGProof
open PI.SwBig
namespace PI.SwBig.BigCellGProof
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n]
    (g H : Matrix n n ℂ) (ρ : n → n) (v : n → ℂ)
    (hg : ∀ b j, g b j = if b = ρ j then v j else 0) (i j : n) :
    (gᴴ * H * g) i j = star (v i) * H (ρ i) (ρ j) * v j := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hg]
  simp [apply_ite star, Finset.sum_ite_eq', ite_mul, mul_ite, Finset.sum_mul]
end PI.SwBig.BigCellGProof
