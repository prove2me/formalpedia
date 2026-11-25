-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FlagGramNonneg.conjT_mul_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:11.378307+00:00
-- url     : https://prove2.me/submissions/d5d3e367-0148-4802-897f-8aebd4aeb03d

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_ConjTMulMulApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PI.FlagGramNonneg
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg
namespace PI.UnitaryGroupMassFormula.FlagGramNonneg
theorem _root_.solution {m n : Type} [Fintype m] (A : Matrix m n ℂ) (B : Matrix m m ℂ) (i j : n) :
    (Aᴴ * B * A) i j = star (fun k => A k i) ⬝ᵥ (B *ᵥ fun k => A k j) := by
  simp only [mul_apply, conjTranspose_apply, dotProduct, mulVec, Pi.star_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
end PI.UnitaryGroupMassFormula.FlagGramNonneg
