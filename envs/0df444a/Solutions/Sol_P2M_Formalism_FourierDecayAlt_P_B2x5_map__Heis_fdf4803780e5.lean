-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_B2x5_map__Heis_fdf4803780e5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:40:55.142059+00:00
-- url     : https://prove2.me/submissions/d14c726c-a9b0-497f-8c9c-428146f6fa53

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_measurable_heisT
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x5__Heis_eq_adc2ccc881fd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution (k r' : ℕ) {Φ : Mt k (1 + r') → Mt k (1 + r')} (hΦ : Measurable Φ) {T : HPar k r' → HPar k r'}
    (hT : MeasurePreserving T volume volume) (h : ∀ x, Φ (heisT k r' x) = heisT k r' (T x)) :
    (μHeis k r').map Φ = μHeis k r' := by
  rw [μHeis_eq, Measure.map_map hΦ (measurable_heisT k r')]
  have hc : Φ ∘ heisT k r' = heisT k r' ∘ T := funext h
  rw [hc, ← Measure.map_map (measurable_heisT k r') hT.measurable, hT.map_eq]
end Formalism.FourierDecayAlt.P.B2x5
