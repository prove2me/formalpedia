-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_DimensionInequality_tower_step_cfa42bc38561
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:03.506948+00:00
-- url     : https://prove2.me/submissions/dbf9848f-6bf5-4ead-875d-f7de5c4c793c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDimensionInequality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDimensionInequalitySteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimensionInequality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
universe u v
open Cardinal
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace DimensionInequality
theorem _root_.solution {A : Type u} {C B : Type v} [CommRing A] [CommRing C]
    [CommRing B] [IsDomain A] [IsDomain C] [IsDomain B] [Algebra A C] [Algebra C B] [Algebra A B]
    [IsScalarTower A C B] (hAC : Function.Injective (algebraMap A C))
    (hCB : Function.Injective (algebraMap C B)) (P : Ideal B) [P.IsPrime] (Q : Ideal C) [Q.IsPrime]
    (p : Ideal A) [p.IsPrime] [P.LiesOver Q] [Q.LiesOver p] [P.LiesOver p]
    (e₁ : ofENat Q.height + Algebra.trdeg (A ⧸ p) (C ⧸ Q) ≤ ofENat p.height + Algebra.trdeg A C)
    (e₂ : ofENat P.height + Algebra.trdeg (C ⧸ Q) (B ⧸ P) ≤ ofENat Q.height + Algebra.trdeg C B) :
    ofENat P.height + Algebra.trdeg (A ⧸ p) (B ⧸ P) ≤ ofENat p.height + Algebra.trdeg A B := by
  have : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).mpr hAC
  have : FaithfulSMul C B := (faithfulSMul_iff_algebraMap_injective C B).mpr hCB
  have : IsScalarTower (A ⧸ p) (C ⧸ Q) (B ⧸ P) := IsScalarTower.of_algebraMap_eq fun x ↦ by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [Ideal.Quotient.algebraMap_mk_of_liesOver, ← IsScalarTower.algebraMap_apply]
  have t₁ := trdeg_add_eq A C (A := B)
  have t₂ := trdeg_add_eq (A ⧸ p) (C ⧸ Q) (A := B ⧸ P)
  calc ofENat P.height + Algebra.trdeg (A ⧸ p) (B ⧸ P)
      = (ofENat P.height + Algebra.trdeg (C ⧸ Q) (B ⧸ P)) + Algebra.trdeg (A ⧸ p) (C ⧸ Q) := by
        rw [← t₂]; ring
    _ ≤ (ofENat Q.height + Algebra.trdeg C B) + Algebra.trdeg (A ⧸ p) (C ⧸ Q) := by gcongr
    _ = (ofENat Q.height + Algebra.trdeg (A ⧸ p) (C ⧸ Q)) + Algebra.trdeg C B := by ring
    _ ≤ (ofENat p.height + Algebra.trdeg A C) + Algebra.trdeg C B := by gcongr
    _ = ofENat p.height + Algebra.trdeg A B := by rw [add_assoc, t₁]
end DimensionInequality
end GroundTheory.Heights₂.Heights.NumbersDVR
