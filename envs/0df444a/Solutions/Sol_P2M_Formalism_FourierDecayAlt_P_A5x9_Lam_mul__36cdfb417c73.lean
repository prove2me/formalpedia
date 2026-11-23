-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_A5x9_Lam_mul__36cdfb417c73
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:09.222896+00:00
-- url     : https://prove2.me/submissions/fcf42962-cb7d-488f-a624-a58bc5f1bb83

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_Lam_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_msk_mulVec
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_mul_inv_one_up


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (Z₀ p : Matrix (Fin n) (Fin n) K) (hp : IsPP R k p) (x : Fin n → R) :
    abelian₂ R k Z₀ x = b22 k p *ᵥ abelian₂ R k (Z₀ * p) x := by
  rw [Lam_apply, Lam_apply, ← msk_mulVec k hp.1.1, Matrix.mul_inv_rev, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, mul_inv_one_up hp.1.1, Matrix.one_mul]
end Formalism.FourierDecayAlt.P.A5x9
