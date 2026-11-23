-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_G7_ae_cof_ne__e121f0100f6f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:42.009122+00:00
-- url     : https://prove2.me/submissions/d19e61b0-db63-4a32-abb3-3fa850d072c9

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_isStrictUpper_strictUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_ae_cof_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_cof

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P.G7
theorem _root_.solution (β t : ℂ) (ht : t ≠ 0) (m : ℕ) :
    ∀ᵐ y ∂((muPi β (Fin m)).prod ((muPi β (UT (m + 1))).prod (muPi β (Fin (m + 1))))),
      Cof (strictUpper y.2.1) y.2.2 t ≠ 0 := by
  have h1 : ∀ᵐ z ∂((muPi β (UT (m + 1))).prod (muPi β (Fin (m + 1)))), Cof (strictUpper z.1) z.2 t ≠ 0 := by
    have hms : MeasurableSet {z : (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) | Cof (strictUpper z.1) z.2 t ≠ 0} :=
      ((isClosed_singleton (x := (0 : ℂ))).preimage (continuous_cof m t)).isOpen_compl.measurableSet
    refine (Measure.ae_prod_iff_ae_ae hms).2 ?_
    refine Filter.Eventually.of_forall fun x => ?_
    filter_upwards [ae_cof_ne β t ht (strictUpper x) (isStrictUpper_strictUpper x)] with B hB
    exact hB
  exact Measure.quasiMeasurePreserving_snd.ae h1
end Formalism.FourierDecayAlt.P.G7
