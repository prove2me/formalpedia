-- Prove2me | solution 1 for WeierstrassProjModel.kw_ev_genericPoint_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/f43f7f02-0658-5c78-89b8-7053a81a5f57

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_exists_pointEval
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Theorems.Thm_WeierstrassProjModel_kw_ev_genericPoint_chartFactor_pointClass_ne_zero
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_ev_genericPoint_ne_zero

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option Elab.async false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem solution [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] :
    haveI : Smooth (projModelStrCR W.toProjective) :=
      (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
    haveI : GeometricallyIntegral (projModelStrCR W.toProjective) :=
      kw_hgi_geometricallyIntegral_of_baseChangeIso W
        (projModel_pullback_iso_baseChange W.toProjective)
    haveI : IsIntegral (projModelCR W.toProjective) :=
      GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (projModelStrCR W.toProjective)
    letI : Algebra R (projModelCR W.toProjective).functionField :=
      (Spec.preimage ((projModelCR W.toProjective).fromSpecStalk
        (genericPoint (projModelCR W.toProjective)) ≫ projModelStrCR W.toProjective)).hom.toAlgebra
    have hΔF : algebraMap R (projModelCR W.toProjective).functionField W.Δ ≠ 0 :=
      (W.isUnit_Δ.map _).ne_zero
    (exists_pointEval W (projModelCR W.toProjective).functionField hΔF).2.2.choose
        ⟨(projModelCR W.toProjective).fromSpecStalk (genericPoint (projModelCR W.toProjective)),
          by
            show (projModelCR W.toProjective).fromSpecStalk _ ≫ projModelStrCR W.toProjective
              = Spec.map (CommRingCat.ofHom (algebraMap R (projModelCR W.toProjective).functionField))
            rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]⟩
      ≠ 0 := by

  haveI : Smooth (projModelStrCR W.toProjective) :=
    (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
  haveI : GeometricallyIntegral (projModelStrCR W.toProjective) :=
    kw_hgi_geometricallyIntegral_of_baseChangeIso W
      (projModel_pullback_iso_baseChange W.toProjective)
  haveI : IsIntegral (projModelCR W.toProjective) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (projModelStrCR W.toProjective)
  letI : Algebra R (projModelCR W.toProjective).functionField :=
    (Spec.preimage ((projModelCR W.toProjective).fromSpecStalk
      (genericPoint (projModelCR W.toProjective)) ≫ projModelStrCR W.toProjective)).hom.toAlgebra
  intro hΔF

  obtain ⟨i, ψ, hfac, hne⟩ := kw_ev_genericPoint_chartFactor_pointClass_ne_zero W
  intro h0
  apply hne

  have hpt := (exists_pointEval W (projModelCR W.toProjective).functionField hΔF).2.2.choose_spec.2
    ⟨(projModelCR W.toProjective).fromSpecStalk (genericPoint (projModelCR W.toProjective)),
      by
        show (projModelCR W.toProjective).fromSpecStalk _ ≫ projModelStrCR W.toProjective
          = Spec.map (CommRingCat.ofHom (algebraMap R (projModelCR W.toProjective).functionField))
        rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]⟩
    i ψ hfac

  exact hpt.symm.trans (h0 ▸ WeierstrassCurve.Projective.Point.zero_point)

end

end S_WeierstrassProjModel_kw_ev_genericPoint_ne_zero
end P2MW
export P2MW.S_WeierstrassProjModel_kw_ev_genericPoint_ne_zero (solution)
