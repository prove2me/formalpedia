-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_isHomogeneous_linPoly_741f83c4b563
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:13.902751+00:00
-- url     : https://prove2.me/submissions/029b7661-1b8e-4308-9a3a-026033f4b0da

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (j : Fin d) :
    (linPoly A j).IsHomogeneous 1 := by
  have : linPoly A j ∈ homogeneousSubmodule (Fin n) ℂ 1 := by
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X ℂ i))
  exact (mem_homogeneousSubmodule 1 _).1 this
end GroundTheory.Heights₂.Heights.ComplexSets
