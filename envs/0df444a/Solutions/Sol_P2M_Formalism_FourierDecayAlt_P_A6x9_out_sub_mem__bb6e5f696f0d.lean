-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_A6x9_out_sub_mem__bb6e5f696f0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:37:11.976719+00:00
-- url     : https://prove2.me/submissions/1a09fef3-2013-4edd-a9f2-927966c48527

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PadicChangeOfVariables

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
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x9
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
variable (π : Kˣ)
namespace Formalism.FourierDecayAlt.P.A6x9
theorem _root_.solution {B : AddSubgroup K} (z : K) :
    (Quotient.out ((z : K) : K ⧸ B) : K) - z ∈ B := by
  have h : ((Quotient.out ((z : K) : K ⧸ B) : K) : K ⧸ B) = ((z : K) : K ⧸ B) :=
    QuotientAddGroup.out_eq' _
  have := (QuotientAddGroup.eq).1 h.symm
  rwa [neg_add_eq_sub] at this
end Formalism.FourierDecayAlt.P.A6x9
