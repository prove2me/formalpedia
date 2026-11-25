-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_OrbitTailEstimates_pow_arith__8930bfb03f06
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:38:01.543853+00:00
-- url     : https://prove2.me/submissions/63584bfd-d4c7-431e-b827-ba2396cdf7b8

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitTailEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_pow_arith

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitTailEstimates
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7
namespace Formalism.FourierDecayAlt.P.OrbitTailEstimates
theorem _root_.solution (m : ℕ) (x : ℝ) (hx : 0 < x) :
    x ^ ((m + 1) ^ 2) * (x ^ ((m + 1) * (m + 4)))⁻¹ = x * (x ^ (3 * m + 4))⁻¹ := by
  have h0 : x ^ (3 * m + 4) ≠ 0 := (pow_pos hx _).ne'
  calc x ^ ((m + 1) ^ 2) * (x ^ ((m + 1) * (m + 4)))⁻¹
      = (x ^ ((m + 1) ^ 2) * ((x ^ ((m + 1) * (m + 4)))⁻¹ * x ^ (3 * m + 4))) * (x ^ (3 * m + 4))⁻¹ := by
        rw [← mul_assoc, mul_assoc _ (x ^ (3 * m + 4)), mul_inv_cancel₀ h0, mul_one]
    _ = _ := by rw [pow_arith m x hx]
end Formalism.FourierDecayAlt.P.OrbitTailEstimates
