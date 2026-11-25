-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_sub__0af415330cc5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:38:05.157211+00:00
-- url     : https://prove2.me/submissions/c1a3d22e-3f43-400b-9f2b-2833d732c5aa

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_rsmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_inLie_rsmul


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LieDecompositionLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.LieDecompositionLocal
theorem _root_.solution {Φ : Mat k r → E} {g X Y : Mat k r} (hloc : Loc 1 Φ g) (hgG : g ∈ GV k r)
    (hX : inLie k r X) (hY : inLie k r Y) : RdV (X - Y) Φ g = RdV X Φ g - RdV Y Φ g := by
  have hY' : inLie k r (((-1 : ℝ) : ℂ) • Y) := B4.inLie_rsmul hY (-1)
  have e : X - Y = X + ((-1 : ℝ) : ℂ) • Y := by simp [sub_eq_add_neg]
  rw [e, rdV_add hloc hgG hX hY', rdV_rsmul hloc hgG hY]
  simp [sub_eq_add_neg]
end Formalism.FourierDecayAlt.P.LieDecompositionLocal
