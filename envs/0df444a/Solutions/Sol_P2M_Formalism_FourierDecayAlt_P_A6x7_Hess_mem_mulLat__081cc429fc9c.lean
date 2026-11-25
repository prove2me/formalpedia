-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_A6x7_Hess_mem_mulLat__081cc429fc9c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:37:10.31626+00:00
-- url     : https://prove2.me/submissions/9c76d10d-d6ea-4be9-92c4-e97419a8e299

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Hess_mem_mulLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_mem_mulLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7 Formalism.FourierDecayAlt.P.A6x7.Hess
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.A6x7.Hess
theorem _root_.solution (b : Kˣ) (L : AddSubgroup K) (x : K) :
    x ∈ mulLat (b : K) L ↔ ((b⁻¹ : Kˣ) : K) * x ∈ L := by
  rw [← mem_mulLat b L, ← mul_assoc, Units.mul_inv, one_mul]
end Formalism.FourierDecayAlt.P.A6x7.Hess
