-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FormalFibresRegular_proof_65ffb8ed20d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:56:57.960199+00:00
-- url     : https://prove2.me/submissions/e2dbe762-48de-468c-8629-301e2d7b2b7d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatNormalFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibresRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibreQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibresRegularPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFormalFibresRegular

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace FormalFibresRegular
theorem _root_.solution (hQ : FormalFibreQuotient.Statement)
    (hP : FormalFibresRegularPolynomial.Statement) : FormalFibresRegular.Statement := by
  intro k A _ _ _ hA m hm P _
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hA
  have hfs : Function.Surjective (f : MvPolynomial (Fin n) k →+* A) := hf
  obtain ⟨P', -, ⟨e⟩⟩ :=
    hQ (MvPolynomial (Fin n) k) A (f : MvPolynomial (Fin n) k →+* A) hfs inferInstance m P
  have hM : (m.comap (f : MvPolynomial (Fin n) k →+* A)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ hfs (H := hm)
  have := hP k n _ hM P'.asIdeal
  exact IsRegularLocalRing.of_ringEquiv e.symm
end FormalFibresRegular
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
