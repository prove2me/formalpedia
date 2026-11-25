-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_JFxB_rho_eq_trn__db6dceb877d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:46:26.440636+00:00
-- url     : https://prove2.me/submissions/6e34fd58-3867-4811-afb1-fe06f697189a

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (p : SS k r) (F : Mat k r → (Wq →L[ℂ] Wp)) :
    rho D p F = trn (Lq D p) ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹) (Matrix.of p.2.2 * Matrix.of p.2.1) F := by
  funext x
  show (D.π (Matrix.of p.1.1)).comp ((F (sgs p x)).comp (D.π' (Matrix.of p.2.1)⁻¹)) =
    (D.π (Matrix.of p.1.1)).comp
      ((F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * x * (Matrix.of p.2.2 * Matrix.of p.2.1))).comp
        (D.π' (Matrix.of p.2.1)⁻¹))
  simp only [sgs, Matrix.mul_assoc]
end Formalism.FourierDecayAlt.P.JFxB
