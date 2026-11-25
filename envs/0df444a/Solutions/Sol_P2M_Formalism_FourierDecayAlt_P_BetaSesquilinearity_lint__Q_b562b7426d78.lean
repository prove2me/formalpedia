-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lint__Q_b562b7426d78
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:37:15.598803+00:00
-- url     : https://prove2.me/submissions/ecb14a98-227e-4a9a-9f1a-f7cc0dda987a

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_wt_measurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Qset_measurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_wt_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (f : (Fin r → ℂ) × ℂ → ℝ≥0∞) :
    ∫⁻ q, f q ∂μQ D = ∫⁻ q, ENNReal.ofReal (wt D q) * f q := by
  unfold μQ
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (wt_measurable D).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← lintegral_indicator (Qset_measurable D)]
  congr 1
  funext q
  by_cases hq : q ∈ Qset D
  · simp [Set.indicator_apply, hq]
  · simp [Set.indicator_apply, hq, wt_eq_zero D hq]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
