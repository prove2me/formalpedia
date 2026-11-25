-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_length_localization_quotient_a5622d7b17c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:05.063934+00:00
-- url     : https://prove2.me/submissions/41c36298-c692-4014-807c-8b23fc4306dc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLengthFiniteAlgebra

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
open IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.LengthFiniteAlgebra
variable {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B]
omit [IsLocalRing O]
namespace GroundTheory.Heights₂.Heights.LengthFiniteAlgebra
theorem _root_.solution (I : Ideal B) (Q : Ideal (B ⧸ I)) [Q.IsMaximal] :
    Module.length O (Localization.AtPrime Q) =
      Module.length O (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))))) := by
  have hsub : Algebra.algebraMapSubmonoid (B ⧸ I) (Q.comap (Ideal.Quotient.mk I)).primeCompl =
      Q.primeCompl := by
    ext y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨x, hx, hxy⟩
      rw [← hxy]
      exact hx
    · intro hy
      exact ⟨y, hy, rfl⟩
  have : IsLocalization Q.primeCompl
      (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))))) := by
    rw [← hsub]; infer_instance
  let e := IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q)
    (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))))
  have : IsScalarTower O (B ⧸ I)
      (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))))) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply O B (B ⧸ I),
        IsScalarTower.algebraMap_apply O (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))),
        IsScalarTower.algebraMap_apply O B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))]
      rfl
  exact (e.toLinearEquiv.restrictScalars O).length_eq
end GroundTheory.Heights₂.Heights.LengthFiniteAlgebra
