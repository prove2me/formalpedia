-- Prove2me | solution 1 for PI.PolynomialProperness.TauW.xiV_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:55:11.429558+00:00
-- url     : https://prove2.me/submissions/0971b1ff-b84c-41c4-a152-bea25e19da0f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_FvecCastSucc

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
open PI PI.PolynomialProperness PI.PolynomialProperness.TauW
namespace PI.PolynomialProperness.TauW
theorem _root_.solution (k r : ℕ) (p : Fin r → ℂ) : xiV k r p = ∑ a, p a • bvec (eI k r a) := by
  ext i
  simp only [xiV, bvec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite,
    mul_one, mul_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i.val, h⟩]
    · rw [if_pos]
      ext
      simp [eI]
    · intro b _ hb
      rw [if_neg]
      intro he
      apply hb
      ext
      simp only [Fin.val_mk]
      have := congrArg Fin.val he
      simp [eI] at this
      omega
    · simp
  · symm
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro he
    apply h
    rw [he]
    simp [eI]
end PI.PolynomialProperness.TauW
