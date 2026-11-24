-- Prove2me | solution 1 for PI.QnRT.lin_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:43:51.119018+00:00
-- url     : https://prove2.me/submissions/7e8d13c3-0e4e-41f5-996a-af3cb0663aad

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_SecondHermitianPartDiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.QnRT
variable {k r : ℕ}
namespace PI.QnRT
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r)
    (L : (Fin r → ℂ) →L[ℝ] E) (z : ℂ) :
    L (Pi.single l z) = (z.re : ℂ) • L (Pi.single l 1) + (z.im : ℂ) • L (Pi.single l Complex.I) := by
  have h : (Pi.single l z : Fin r → ℂ) =
      ((z.re : ℝ) • (Pi.single l (1 : ℂ) : Fin r → ℂ) +
        (z.im : ℝ) • (Pi.single l Complex.I : Fin r → ℂ) : Fin r → ℂ) := by
    ext i
    by_cases hi : i = l
    · subst hi
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Complex.real_smul, mul_one]
      exact (Complex.re_add_im z).symm
    · simp [hi]
  rw [h, map_add, map_smul, map_smul, Complex.coe_smul, Complex.coe_smul]
end PI.QnRT
