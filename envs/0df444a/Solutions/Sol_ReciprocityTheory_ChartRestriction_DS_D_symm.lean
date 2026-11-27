-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.D_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:24:31.588669+00:00
-- url     : https://prove2.me/submissions/3d3e53bf-440e-4bad-8c87-452f5e0f3986

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_inner_dOp_left
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_inner_dOp__left_4a52bdd93724

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ε : Fin n → Bool} {E cp cm : Fin n → Fin n → Module.End ℂ W} (hU : IsInfUnitary ε E)
    (hEC : CommutesCAR E cp cm) (hadj : ∀ (i a : Fin n) (x y : W), inner ℂ (cp i a x) y = inner ℂ x (cm i a y)) (x y : W) :
    inner ℂ ((dOp ε E cp + dOp' ε E cm) x) y = inner ℂ x ((dOp ε E cp + dOp' ε E cm) y) := by
  rw [LinearMap.add_apply, LinearMap.add_apply, inner_add_left, inner_add_right,
    inner_dOp_left hU hEC hadj, inner_dOp'_left hU hEC hadj, add_comm]
end ReciprocityTheory.ChartRestriction.DS
