-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SecFiniteUnit_lineSub_coeff_4e9a91de44a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:54:05.52586+00:00
-- url     : https://prove2.me/submissions/9a0c9cb8-fd6d-4d86-9cae-ee91fa30a73f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecFiniteUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_AssemblyPartial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSecFiniteUnit

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
open MvPolynomial Vertical
noncomputable section
open GroundTheory.Heights₂.Heights.SecFiniteUnit
variable {k R : Type} [Field k] [CommRing R] [Algebra k R] {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.SecFiniteUnit
theorem _root_.solution (y : Par e n → R) (m : Fin n) (ij : Fin (e + 1) × Fin n) :
    (lineSub y m ij).coeff (groupWeight (e + 1) n ij 0) = lineTop y ij := by
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero =>
    simp only [lineSub, lineTop, Fin.cases_zero, groupWeight, Pi.single_eq_same]
    split_ifs <;> simp [Polynomial.coeff_one]
  | succ i => simp [lineSub, lineTop, groupWeight, Fin.succ_ne_zero]
end GroundTheory.Heights₂.Heights.SecFiniteUnit
