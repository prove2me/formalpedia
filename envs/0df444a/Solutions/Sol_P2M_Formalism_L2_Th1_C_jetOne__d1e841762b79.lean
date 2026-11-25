-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_C_jetOne__d1e841762b79
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:40:37.230375+00:00
-- url     : https://prove2.me/submissions/bb4a52f0-148c-4a72-9d98-336274a0d848

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
import Theorems.Thm_P2M_Formalism_L2_Th1_C_jetNorm__eafef558ccec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open JetSubstitutionLemmas
namespace Formalism.L2.Th1.C
theorem _root_.solution : JetOne := by
  intro K _ _ R l linv ph h hl hph hN h2
  have := jetNorm' K R l linv ph (-1) (-1) h hl hph hN 1 le_rfl
  have e : jet l ph 1 = (((-1 : K) ^ 1 - (-1) * (-1)) * jet l ph 1) * (-(2 : K)⁻¹) := by
    rw [show ((-1 : K) ^ 1 - (-1) * (-1)) = -2 by norm_num]
    rw [show (-2 : K) * jet l ph 1 * -(2 : K)⁻¹ = (2 * (2 : K)⁻¹) * jet l ph 1 by ring,
      mul_inv_cancel₀ two_ne_zero, one_mul]
  rw [e]
  exact mul_mem this (neg_mem h2)
end Formalism.L2.Th1.C
