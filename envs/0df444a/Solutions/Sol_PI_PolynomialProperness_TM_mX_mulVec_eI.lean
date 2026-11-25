-- Prove2me | solution 1 for PI.PolynomialProperness.TM.mX_mulVec_eI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:27:57.191121+00:00
-- url     : https://prove2.me/submissions/64027cdc-64e7-4cae-83e2-1c638c5d4b18

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_MXMulVecMid
import Theorems.Thm_PI_PolynomialProperness_TM_sum_emb
import Theorems.Thm_PI_PolynomialProperness_TM_mX_eI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.TM
namespace PI.PolynomialProperness.TM
theorem _root_.solution (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) (x : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (mX k r vX *ᵥ x) (eI k r a) = (vX *ᵥ pX k r x) a := by
  simp only [Matrix.mulVec, dotProduct, mX_eI]
  refine (sum_emb (eIe k r) _ ?_).trans ?_
  · intro i hi
    by_cases h : i.val < r
    · exact absurd (Fin.ext rfl : eIe k r ⟨i.val, h⟩ = i) (hi _)
    · rw [dif_neg h, zero_mul]
  · apply Finset.sum_congr rfl
    intro t _
    have hc : ((eIe k r) t).val < r := t.isLt
    rw [dif_pos hc]
    rfl
end PI.PolynomialProperness.TM
