-- Prove2me | solution 1 for WeierstrassCurve.exists_addEquiv_point_baseChange_variableChange_smul_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/9f980d52-af45-58dd-8b36-299c979bed84

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_of_variableChange_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_addEquiv_point_baseChange_variableChange_smul_algEquiv

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
    (W : WeierstrassCurve F) (γ : WeierstrassCurve.VariableChange F) :
    ∃ φ : ((γ • W).baseChange K).toAffine.Point ≃+ (W.baseChange K).toAffine.Point,
      ∀ (σ : K ≃ₐ[F] K) (P : ((γ • W).baseChange K).toAffine.Point), φ (σ • P) = σ • φ P :=
  WeierstrassCurve.exists_addEquiv_point_of_variableChange_eq K γ⁻¹ (inv_smul_smul γ W)

end S_WeierstrassCurve_exists_addEquiv_point_baseChange_variableChange_smul_algEquiv
end P2MW
export P2MW.S_WeierstrassCurve_exists_addEquiv_point_baseChange_variableChange_smul_algEquiv (solution)
