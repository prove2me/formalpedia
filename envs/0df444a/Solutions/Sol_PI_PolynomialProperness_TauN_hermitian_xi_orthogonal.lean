-- Prove2me | solution 1 for PI.PolynomialProperness.TauN.hermitian_xi_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:04:26.458498+00:00
-- url     : https://prove2.me/submissions/05b01b9b-dcc0-4945-87a7-60e06de5a8ca

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermitianXiOrthogonal
import Theorems.Thm_PI_PolynomialProperness_TauN_xiV_hi
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_Hpk_eq
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq


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
open PI PI.PolynomialProperness PI.PolynomialProperness.TauN
namespace PI.PolynomialProperness.TauN
theorem _root_.solution (k r : ℕ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (p : Fin r → ℂ) :
    herm (Hpk k r) (xiV k r p) z = 0 := by
  unfold herm
  simp only [dotProduct]
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [Pi.star_apply, hz i h, star_zero, zero_mul]
  · have hs : GBasic.sig k r i = i := by
      unfold GBasic.sig
      rw [if_neg h]
    have hx : (Hpk k r *ᵥ xiV k r p) i = 0 := by
      simp only [Matrix.mulVec, dotProduct, GBasic.Hpk_eq, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, hs, xiV_hi k r p i (by omega), mul_zero]
    rw [hx, mul_zero]
end PI.PolynomialProperness.TauN
