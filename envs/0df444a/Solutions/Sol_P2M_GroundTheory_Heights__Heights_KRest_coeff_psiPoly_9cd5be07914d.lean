-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KRest_coeff_psiPoly_9cd5be07914d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:42.273958+00:00
-- url     : https://prove2.me/submissions/06bb3704-a126-4468-bddb-0db787049596

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RestCutBasic

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
open GroundTheory.Heights₂.Heights.KRest
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.KRest
theorem _root_.solution {σ : Type*} (ψ : ℝ →ₗ[ℚ] ℚ) (P : MvPolynomial σ ℝ) (β : σ →₀ ℕ) :
    coeff β (psiPoly ψ P) = ψ (coeff β P) :=
  coeff_psiPolyFun ψ P β
end GroundTheory.Heights₂.Heights.KRest
