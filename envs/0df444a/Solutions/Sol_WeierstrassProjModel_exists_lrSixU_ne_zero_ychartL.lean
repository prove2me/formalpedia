-- Prove2me | solution 1 for WeierstrassProjModel.exists_lrSixU_ne_zero_ychartL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/09a18264-ccf3-5ecf-a5bf-b1b87ab2f764

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_kw_lrSixU_addZ_ne_zero_ychartL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_lrSixU_ne_zero_ychartL

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem solution [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] (j : Fin 3) :
    ∃ l, kw_lrSixU W 1 j l ≠ 0 :=
  ⟨.inl 2, kw_lrSixU_addZ_ne_zero_ychartL W j⟩

end

end S_WeierstrassProjModel_exists_lrSixU_ne_zero_ychartL
end P2MW
export P2MW.S_WeierstrassProjModel_exists_lrSixU_ne_zero_ychartL (solution)
