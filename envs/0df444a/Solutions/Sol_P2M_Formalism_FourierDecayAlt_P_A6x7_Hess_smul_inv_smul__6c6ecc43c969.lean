-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_A6x7_Hess_smul_inv_smul__6c6ecc43c969
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:37:11.147628+00:00
-- url     : https://prove2.me/submissions/fca02a5f-dda9-41cd-a0b4-e9fa6962e907

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice

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
theorem _root_.solution (b : Kˣ) {d : ℕ} (x : Fin d → K) :
    (b : K) • (((b⁻¹ : Kˣ) : K) • x) = x := by
  rw [smul_smul, Units.mul_inv, one_smul]
end Formalism.FourierDecayAlt.P.A6x7.Hess
