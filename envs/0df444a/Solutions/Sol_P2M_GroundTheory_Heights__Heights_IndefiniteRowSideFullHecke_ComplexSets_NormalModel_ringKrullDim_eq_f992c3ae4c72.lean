-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModel_ringKrullDim_eq_f992c3ae4c72
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:00.95512+00:00
-- url     : https://prove2.me/submissions/fa92eac9-d160-4ff1-87c3-bfbd4ed034ee

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelOpenMapping
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocallyIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericProjectionFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionsContainOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PUnitaryZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDiscriminantCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelOpenMapping
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mul
import Theorems.Thm_GroundTheory_Arith_Toric_ringKrullDim_eq_of_isIntegral


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
open MvPolynomial Topology Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace NormalModel
theorem _root_.solution {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : NormalModel J) :
    ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) =
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) := by
  let _ : Algebra (MvPolynomial (Fin n) ℂ ⧸ J) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) :=
    M.quotMap.toAlgebra
  have hf : ∀ q, algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal)
      (Ideal.Quotient.mk J q) = Ideal.Quotient.mk M.ideal (rename Sum.inl q) := fun q =>
    Ideal.quotientMap_mk (H := M.le_comap)
  have hint : ∀ q : MvPolynomial (Fin n ⊕ Fin M.m) ℂ,
      IsIntegral (MvPolynomial (Fin n) ℂ ⧸ J) (Ideal.Quotient.mk M.ideal q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c =>
      have : Ideal.Quotient.mk M.ideal (C c) = algebraMap _ _ (Ideal.Quotient.mk J (C c)) := by
        rw [hf, rename_C]
      rw [this]
      exact isIntegral_algebraMap
    | add p q hp hq =>
      rw [map_add]
      exact hp.add hq
    | mul_X p i hp =>
      rw [map_mul]
      refine hp.mul ?_
      rcases i with j | j
      · have : Ideal.Quotient.mk M.ideal (X (Sum.inl j)) = algebraMap _ _ (Ideal.Quotient.mk J (X j)) := by
          rw [hf, rename_X]
        rw [this]
        exact isIntegral_algebraMap
      · obtain ⟨P, hPm, hP⟩ := M.integral j
        refine ⟨P.map (Ideal.Quotient.mk J), hPm.map _, ?_⟩
        rw [Polynomial.eval₂_map]
        have hcomp : (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal)).comp
            (Ideal.Quotient.mk J) = (Ideal.Quotient.mk M.ideal).comp
              (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom :=
          RingHom.ext fun q => hf q
        rw [hcomp, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
        exact hP
  have : Algebra.IsIntegral (MvPolynomial (Fin n) ℂ ⧸ J) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) :=
    ⟨fun x => by
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact hint q⟩
  exact GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral
    (Ideal.quotientMap_injective' (H := M.le_comap) (fun q hq => by rw [← M.comap_eq]; exact hq))
end NormalModel
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
