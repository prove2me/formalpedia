-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.Q_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:02.740244+00:00
-- url     : https://prove2.me/submissions/931e58b4-9b61-4a96-86f7-44a05c2808ba

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_polar_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Matrix
variable {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (A B : Matrix (Fin d) (Fin d) ℝ) (hAB : A = Bᴴ * B) (x : Fin d → ℤ) :
    Q A x = ‖fB B x‖ ^ 2 / 2 := by
  rw [Q, polar_eq A B hAB, real_inner_self_eq_norm_sq]
end ReciprocityTheory.ReducedBases.T2
