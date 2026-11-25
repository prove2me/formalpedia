-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Ux1_rsmul_cancel__96098f4791bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:00.74208+00:00
-- url     : https://prove2.me/submissions/955a626b-2b8d-4e7a-ba8e-425a9de6e2d3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution {g : Mat k r} (hg : g ∈ GV k r) (a : ℝ) (e : E) :
    ((gN g ^ a : ℝ) : ℂ) • ((gN g ^ (-a) : ℝ) : ℂ) • e = e := by
  rw [smul_smul, ← Complex.ofReal_mul, ← Real.rpow_add (gN_pos hg), add_neg_cancel, Real.rpow_zero,
    Complex.ofReal_one, one_smul]
end Formalism.FourierDecayAlt.P.Ux1
