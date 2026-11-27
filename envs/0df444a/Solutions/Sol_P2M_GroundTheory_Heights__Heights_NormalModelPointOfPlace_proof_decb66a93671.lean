-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalModelPointOfPlace_proof_decb66a93671
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:14:28.53341+00:00
-- url     : https://prove2.me/submissions/abcd37d5-102c-4e9d-8c79-69a882d63953

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPointOfPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StModelLocalizationMaximalPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalizationAtPrimeQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelPointOfPlace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ord_ringEquiv_ad3b8618db20


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace NormalModelPointOfPlace
theorem _root_.solution (hLoc : NormalisationModelLocalization.Statement)
    (hMax : ModelLocalizationMaximalPoint.Statement) (hAt : LocalizationAtPrimeQuotient.Statement.{0}) :
    NormalModelPointOfPlace.Statement := by
  intro n J q M hJ P
  obtain ⟨e, he⟩ := hLoc n J q M hJ
  obtain ⟨P', hP'def⟩ : ∃ P' : @Ideal (Localization (normalModelSubmonoid M q)) CommSemiring.toSemiring,
      P' = P.asIdeal.comap (e.symm : Localization (normalModelSubmonoid M q) →+* curveNormalisation J q) :=
    ⟨_, rfl⟩
  have hP' : P'.IsMaximal := by
    rw [hP'def]
    exact Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  have hPp : P'.IsPrime := by
    rw [hP'def]
    infer_instance
  obtain ⟨w, hw, hq, hcomap⟩ := hMax n J q M P' hP'
  obtain ⟨eAt, heAt⟩ := hAt (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) M.ideal (normalModelSubmonoid M q) P'
    (RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)) hcomap
  let eP : Localization.AtPrime P.asIdeal ≃+* Localization.AtPrime P' :=
    IsLocalization.ringEquivOfRingEquiv (M := P.asIdeal.primeCompl) (T := P'.primeCompl)
      (Localization.AtPrime P.asIdeal) (Localization.AtPrime P') e (by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          subst hP'def
          show e.symm (e x) ∉ P.asIdeal
          simpa using hx
        · intro hy
          subst hP'def
          exact ⟨e.symm y, hy, by simp⟩)
  refine ⟨w, hw, hq, fun f ↦ ?_⟩
  rw [← ord_ringEquiv (eP.trans eAt)]
  congr 1
  rw [RingEquiv.trans_apply, IsLocalization.ringEquivOfRingEquiv_eq, he, heAt]
  rfl
end NormalModelPointOfPlace
end GroundTheory.Heights₂.Heights
