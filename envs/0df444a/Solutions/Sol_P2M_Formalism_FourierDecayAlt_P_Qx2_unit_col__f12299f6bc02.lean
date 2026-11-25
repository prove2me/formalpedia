-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Qx2_unit_col__f12299f6bc02
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:47:08.33044+00:00
-- url     : https://prove2.me/submissions/8a6ab560-0ed6-4eb7-b24a-b60e4c64b72c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpk_out

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution {i : Fin (r + 1)} {a b p : Fin (2 * r + k + 1)} (ha : inV k r i a) (hp : ¬ inV k r i p) :
    (Hpk k r * (Matrix.single a b (1 : ℂ) : Mx k r)ᴴ * Hpk k r) *ᵥ bvec p = 0 := by
  have h0 : Hpk k r a p = 0 := hpk_out ha hp
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have h1 : (Matrix.single a b (1 : ℂ) : Mx k r)ᴴ *ᵥ (Hpk k r *ᵥ bvec p) = 0 := by
    ext q
    simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.single_apply, bvec,
      Pi.single_apply, h0]
    refine Finset.sum_eq_zero fun c _ => ?_
    split_ifs with hc
    · rw [← hc.1]
      exact h0
    · rfl
  rw [h1, Matrix.mulVec_zero]
end Formalism.FourierDecayAlt.P.Qx2
