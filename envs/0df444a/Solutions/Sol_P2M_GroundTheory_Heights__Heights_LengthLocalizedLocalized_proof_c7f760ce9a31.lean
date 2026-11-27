-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthLocalizedLocalized_proof_c7f760ce9a31
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:03:26.089117+00:00
-- url     : https://prove2.me/submissions/5e1eea39-7259-46ec-8178-70b9455a8414

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedLocalized
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthLocalizedLocalized
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthLocalizedLocalized_isLocalization_atPrime_map_d0de3ab17027

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
universe u v
namespace GroundTheory.Heights₂.Heights
namespace LengthLocalizedLocalized
theorem _root_.solution : LengthLocalizedLocalized.Statement.{u, v} := by
  intro B _ P Q _ _ _ M _ _ hPQ
  have hloc := LengthLocalizedLocalized.isLocalization_atPrime_map B P Q hPQ

  let σ : Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))) ≃ₐ[B]
      Localization.AtPrime P := IsLocalization.algEquiv P.primeCompl _ _
  let : Algebra (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (Localization.AtPrime P) := σ.toRingHom.toAlgebra
  let : Module (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (LocalizedModule P.primeCompl M) :=
    Module.compHom _ (algebraMap (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (Localization.AtPrime P))
  have : IsScalarTower (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
    ⟨fun r l x => by
      show (r • l) • x = algebraMap _ (Localization.AtPrime P) r • (l • x)
      rw [Algebra.smul_def, mul_smul]⟩
  have : IsScalarTower B (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (LocalizedModule P.primeCompl M) :=
    ⟨fun b r x => by
      show algebraMap _ (Localization.AtPrime P) (b • r) • x =
        b • (algebraMap _ (Localization.AtPrime P) r • x)
      rw [Algebra.smul_def, map_mul, mul_smul]
      rw [show algebraMap (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
          (Localization.AtPrime P) (algebraMap B _ b) = algebraMap B (Localization.AtPrime P) b from
          σ.commutes b, algebraMap_smul]⟩

  have hf : IsBaseChange (Localization.AtPrime Q) (LocalizedModule.mkLinearMap Q.primeCompl M) :=
    IsLocalizedModule.isBaseChange Q.primeCompl _ _
  have hg : IsBaseChange (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (LocalizedModule.mkLinearMap (P.map (algebraMap B (Localization.AtPrime Q))).primeCompl
        (LocalizedModule Q.primeCompl M)) :=
    IsLocalizedModule.isBaseChange (P.map (algebraMap B (Localization.AtPrime Q))).primeCompl _ _
  have hfg := hf.comp hg
  have h0 : IsBaseChange (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (LocalizedModule.mkLinearMap P.primeCompl M) :=
    IsLocalizedModule.isBaseChange P.primeCompl _ _
  rw [← (h0.equiv.symm.trans hfg.equiv).length_eq]
  exact Module.length_eq_of_surjective σ.surjective
end LengthLocalizedLocalized
end GroundTheory.Heights₂.Heights
