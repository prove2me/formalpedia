-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isAffVariety_line_802a8f8c9f87
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:15.105829+00:00
-- url     : https://prove2.me/submissions/9bc470d2-aeeb-4ab2-8c0e-79155b8a85db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PlaneIdealTwoOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial MeasureTheory
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution :
    IsAffVariety (Ideal.span {X 0 - 1} : Ideal (MvPolynomial (Fin 2) ℂ)) 1 := by
  let E := finSuccEquiv ℂ 1
  have hmap : (Ideal.span {Polynomial.X - Polynomial.C (1 : MvPolynomial (Fin 1) ℂ)} :
      Ideal (Polynomial (MvPolynomial (Fin 1) ℂ))) =
      (Ideal.span {X 0 - 1} : Ideal (MvPolynomial (Fin 2) ℂ)).map (E : MvPolynomial (Fin 2) ℂ →+* _) := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    simp [E, finSuccEquiv_X_zero]
  let e : MvPolynomial (Fin 2) ℂ ⧸ (Ideal.span {X 0 - 1} : Ideal (MvPolynomial (Fin 2) ℂ)) ≃+*
      MvPolynomial (Fin 1) ℂ :=
    (Ideal.quotientEquiv _ _ E.toRingEquiv hmap).trans
      (Polynomial.quotientSpanXSubCAlgEquiv (1 : MvPolynomial (Fin 1) ℂ)).toRingEquiv
  refine ⟨?_, ?_⟩
  · have : IsDomain (MvPolynomial (Fin 2) ℂ ⧸ (Ideal.span {X 0 - 1} : Ideal (MvPolynomial (Fin 2) ℂ))) :=
      e.toMulEquiv.isDomain _
    exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  · rw [ringKrullDim_eq_of_ringEquiv e, MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field]
    simp
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
