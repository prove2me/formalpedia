-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_trdeg_polynomial_a210957d600c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:09:53.158014+00:00
-- url     : https://prove2.me/submissions/474ece1d-01cf-4a9c-a21e-b5fa0f047ce2

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Algebra Cardinal
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.DimTie
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.DimTie
theorem _root_.solution (D : Type w) [CommRing D] [IsDomain D] [Algebra k D] [FaithfulSMul k D] :
    trdeg k (Polynomial D) = trdeg k D + 1 := by
  have : FaithfulSMul D (Polynomial D) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Polynomial.C_injective
  rw [← trdeg_add_eq k D (A := Polynomial D), Polynomial.trdeg_of_isDomain]
end GroundTheory.Heights₂.Heights.Kleiman.DimTie
