-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointModel_ringKrullDim_join_ae569ee243f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:11:18.455254+00:00
-- url     : https://prove2.me/submissions/c847131e-fe1b-4a22-a9b5-afab17d95e34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinPointModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointModel_mem_pointIdeal_join_iff_22ed8647669f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord joinCoord mcMap)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointModel
variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointModel
theorem _root_.solution [IsNoetherianRing O] (y : (Σ k, ι k) → Ω) :
    ringKrullDim (MRing (Sum.elim ι ptIdx) O ⧸ pointIdeal O (joinCoord y (ptCoord (Ω := Ω)))) =
      ringKrullDim (MRing ι O ⧸ pointIdeal O y) + 1 := by
  let J := RingHom.ker (Polynomial.mapRingHom (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω))
  let Φ : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O →+* Polynomial (MvPolynomial (Σ k, ι k) O) ⧸ J :=
    (Ideal.Quotient.mk J).comp (srcEquiv (K := K) (ι := ι) O).toRingEquiv.toRingHom
  have hΦ : Function.Surjective Φ := Ideal.Quotient.mk_surjective.comp (srcEquiv O).surjective
  have hker : pointIdeal O (joinCoord y (ptCoord (Ω := Ω))) = RingHom.ker Φ := by
    ext p
    rw [mem_pointIdeal_join_iff, RingHom.mem_ker (f := Φ)]
    change _ ↔ Ideal.Quotient.mk J (srcEquiv O p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
  have hJ : J = (pointIdeal O y).map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) := by
    simp only [J]
    rw [Polynomial.ker_mapRingHom]
    rfl
  have hq : ringKrullDim (MRing (Sum.elim ι ptIdx) O ⧸ RingHom.ker Φ) =
      ringKrullDim (Polynomial (MvPolynomial (Σ k, ι k) O) ⧸ J) :=
    ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hΦ)
  have hp : ringKrullDim (Polynomial (MRing ι O ⧸ pointIdeal O y)) =
      ringKrullDim (Polynomial (MRing ι O) ⧸ (pointIdeal O y).map (Polynomial.C : MRing ι O →+* _)) :=
    ringKrullDim_eq_of_ringEquiv (Ideal.polynomialQuotientEquivQuotientPolynomial (pointIdeal O y))
  rw [hker, hq, hJ, ← hp, Polynomial.ringKrullDim_of_isNoetherianRing]
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointModel
