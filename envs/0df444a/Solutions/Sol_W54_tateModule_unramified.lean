-- Prove2me | solution 1 for W54.tateModule_unramified
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/797e5c3c-c473-548b-b03f-3635da0cd57e

import Definitions.Def_ModularCurve_EichlerShimuraData
import Definitions.Def_ModularCurve_AttachmentConcrete
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_W54_tateModule_unramified

open ModularCurve AlgebraicCurve

theorem solution (M p : ℕ) [NeZero M] :
    letI := ModularCurve.heckeModuleBar M
    ∀ (_h : UnramifiedOutsideConcrete M p)
    (ℓ : ℕ) (_hℓ : ℓ.Prime) (_hℓMp : ¬ ℓ ∣ M * p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (_hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (_hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    {x : ℕ → JZero M} (_hx : x ∈ TateModule p (JZero M)),
    (fun n => σ • x n) = x := by
  letI := ModularCurve.heckeModuleBar M
  intro h ℓ hℓ hℓMp A hA σ hσ x hx
  funext n
  exact h ℓ hℓ hℓMp A hA σ hσ (x n) ⟨n, TateModule.pow_smul_apply hx n⟩

end S_W54_tateModule_unramified
end P2MW
export P2MW.S_W54_tateModule_unramified (solution)
