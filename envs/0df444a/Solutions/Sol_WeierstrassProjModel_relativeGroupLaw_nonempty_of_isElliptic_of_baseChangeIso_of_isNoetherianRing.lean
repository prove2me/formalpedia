-- Prove2me | solution 1 for WeierstrassProjModel.relativeGroupLaw_nonempty_of_isElliptic_of_baseChangeIso_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a6d1d505-6a3c-59cc-81d7-c01f3cd2ff62

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Theorems.Thm_WeierstrassProjModel_exists_thirdLaw_nineCoverage_of_isElliptic_of_isDomain
import Theorems.Thm_WeierstrassProjModel_relativeGroupLaw_nonempty_of_thirdLaw_nineCoverage
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_relativeGroupLaw_nonempty_of_isElliptic_of_baseChangeIso_of_isNoetherianRing
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrThird_substHom_X"

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (V : WeierstrassCurve.Projective R)
    [V.toAffine.IsElliptic]
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
        Nonempty (pullback (projModelStrCR V)
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ≅ projModelCR (V.baseChange K))) :
    Nonempty (RelativeGroupLaw R (projModelStrCR V)) := by
  clear hbc
  obtain ⟨u₃, toE₃, hcov₉, hcompat₃⟩ :=
    WeierstrassProjModel.exists_thirdLaw_nineCoverage_of_isElliptic_of_isDomain V.toAffine
  exact WeierstrassProjModel.relativeGroupLaw_nonempty_of_thirdLaw_nineCoverage
    V.toAffine u₃ toE₃ hcov₉ hcompat₃

end S_WeierstrassProjModel_relativeGroupLaw_nonempty_of_isElliptic_of_baseChangeIso_of_isNoetherianRing
end P2MW
export P2MW.S_WeierstrassProjModel_relativeGroupLaw_nonempty_of_isElliptic_of_baseChangeIso_of_isNoetherianRing (solution)
