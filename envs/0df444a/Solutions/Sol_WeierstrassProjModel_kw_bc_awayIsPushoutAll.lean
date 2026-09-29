-- Prove2me | solution 1 for WeierstrassProjModel.kw_bc_awayIsPushoutAll
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/1ed2ff75-3844-5ac7-bfd2-47dfa298ca3f

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_kw_bc_awayIsPushout_Y
import Theorems.Thm_WeierstrassProjModel_kw_bc_awayIsPushout_Z
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_bc_awayIsPushoutAll

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial HomogeneousLocalization HomogeneousIdealQuotientGrading

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution {R : Type} [CommRing R]
    (W : WeierstrassCurve R) (K : Type) [CommRing K] [Algebra R K] (i : Fin 2) :
    let ψ : projModelGradingCR W.toProjective →+*ᵍ
        projModelGradingCR (W.map (algebraMap R K)).toProjective :=
      { toRingHom := Ideal.quotientMap _ (MvPolynomial.map (algebraMap R K)) <| by
          rw [projModelHomogeneousIdealCR_toIdeal, projModelHomogeneousIdealCR_toIdeal]
          have h : (Ideal.span {W.toProjective.polynomial}).map
                (MvPolynomial.map (algebraMap R K))
              = Ideal.span {(W.map (algebraMap R K)).toProjective.polynomial} := by
            rw [Ideal.map_span, Set.image_singleton,
              WeierstrassCurve.Projective.map_polynomial]
          rw [← h]
          exact Ideal.le_comap_map,
        map_mem := by
          rintro n _ ⟨p, hp, rfl⟩
          exact mk_mem_quotGradingSubmodule _ _
            ((mem_homogeneousSubmodule _ _).mpr
              (((mem_homogeneousSubmodule _ _).mp hp).map (algebraMap R K))) }
    IsPullback
      (Spec.map (CommRingCat.ofHom (Away.map ψ
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (X (![1, 2] i) : MvPolynomial (Fin 3) R)))))
      (Spec.map (CommRingCat.ofHom
        ((fromZeroRingHom (projModelGradingCR (W.map (algebraMap R K)).toProjective)
            (Submonoid.powers (ψ (Ideal.Quotient.mk _
              (X (![1, 2] i) : MvPolynomial (Fin 3) R))))).comp
          (algebraMap K ↥(projModelGradingCR (W.map (algebraMap R K)).toProjective 0)))))
      (Spec.map (CommRingCat.ofHom
        ((fromZeroRingHom (projModelGradingCR W.toProjective)
            (Submonoid.powers (Ideal.Quotient.mk _
              (X (![1, 2] i) : MvPolynomial (Fin 3) R)))).comp
          (algebraMap R ↥(projModelGradingCR W.toProjective 0)))))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  intro ψ
  fin_cases i <;> simp only [Fin.isValue]
  · exact kw_bc_awayIsPushout_Y W K
  · exact kw_bc_awayIsPushout_Z W K

end S_WeierstrassProjModel_kw_bc_awayIsPushoutAll
end P2MW
export P2MW.S_WeierstrassProjModel_kw_bc_awayIsPushoutAll (solution)
