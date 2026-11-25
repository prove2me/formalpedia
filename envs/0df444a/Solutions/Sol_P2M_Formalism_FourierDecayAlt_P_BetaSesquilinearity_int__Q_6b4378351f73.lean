-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_BetaSesquilinearity_int__Q_6b4378351f73
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:37:14.810477+00:00
-- url     : https://prove2.me/submissions/3d2421f6-6ab1-4c49-a141-9063aaef0114

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_wt_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_wt_measurable
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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (f : (Fin r → ℂ) × ℂ → ℂ) :
    ∫ q, f q ∂μQ D = ∫ q, (wt D q : ℂ) * f q := by
  unfold μQ
  rw [integral_withDensity_eq_integral_toReal_smul (wt_measurable D).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun q hq => by rw [wt_eq_zero D hq]; simp)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [ENNReal.toReal_ofReal (wt_nonneg D q), Complex.real_smul]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
