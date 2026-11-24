-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_det_gram_comp_equiv_8c428ade5abb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:10.076659+00:00
-- url     : https://prove2.me/submissions/f92eb4f5-1db3-43bf-b90d-158d08736d5b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension

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
open Matrix
open scoped ComplexOrder
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (w : ι → V) : det (gram ℂ (w ∘ e)) = det (gram ℂ w) := by
  have : gram ℂ (w ∘ e) = (gram ℂ w).submatrix e e := by ext i j; rfl
  rw [this, det_submatrix_equiv_self]
end GroundTheory.Heights₂.Heights
