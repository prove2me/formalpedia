-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_eval_pderiv_sum_mul_8d82014868a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:18:25.286838+00:00
-- url     : https://prove2.me/submissions/5c8f8b95-3f66-4d96-ab13-64344751c68a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StJacobianRankOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameJacobianGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PJacobianRankGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PConormalGenerationGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PJacobianRankOffHypersurface

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace JacobianRankOffHypersurface
theorem _root_.solution {σ ι : Type*} [Fintype ι] (w : σ → ℂ)
    (c g : ι → MvPolynomial σ ℂ) (hg : ∀ k, eval w (g k) = 0) (x : σ) :
    eval w (pderiv x (∑ k, c k * g k)) = ∑ k, eval w (c k) * eval w (pderiv x (g k)) := by
  simp [map_sum, Derivation.leibniz, smul_eq_mul, hg]
end JacobianRankOffHypersurface
end GroundTheory.Heights₂.Heights
