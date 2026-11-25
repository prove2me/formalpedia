-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_GroupGeneratedByExp_norm_pow_mul_le__5d724b404c11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:09:06.59954+00:00
-- url     : https://prove2.me/submissions/51c1ee82-8a98-47d4-b52e-361a94671f84

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GroupGeneratedByExp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_Rep_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open Formalism.FourierDecayAlt.P.GroupGeneratedByExp
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
namespace Formalism.FourierDecayAlt.P.GroupGeneratedByExp
theorem _root_.solution {a : 𝔸} {q : ℝ} (hq : 0 ≤ q) (ha : ∀ u, ‖a * u‖ ≤ q * ‖u‖) (m : ℕ) (u : 𝔸) :
    ‖a ^ m * u‖ ≤ q ^ m * ‖u‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, pow_succ', mul_assoc]
    exact (ha _).trans (mul_le_mul_of_nonneg_left ih hq)
end Formalism.FourierDecayAlt.P.GroupGeneratedByExp
