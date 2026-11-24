-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_blockNonzero_sigma_8db15361a0fa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:44.747439+00:00
-- url     : https://prove2.me/submissions/4449e5c3-76b4-4853-995a-739786e30dc1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coordVec_ne_zero_81a696e5203c

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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x)
    (σ : coordField x →+* ℂ) : BlockNonzero (fun k i ↦ σ (coordVec x k i)) := by
  intro k h
  apply coordVec_ne_zero hx k
  funext i
  exact (map_eq_zero σ).mp (congrFun h i)
end GroundTheory.Heights₂.Heights
