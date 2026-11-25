-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthCutGlobal_smul_injective_pi_30b5f54dca6a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:56.006551+00:00
-- url     : https://prove2.me/submissions/9d389af5-1add-49de-94d9-acb493346596

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutGlobal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthCutGlobal

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
open scoped Pointwise
universe u v
open GroundTheory.Heights₂.Heights.LengthCutGlobal
variable {C : Type u} [CommRing C] (P : Ideal C) [P.IsPrime]
namespace GroundTheory.Heights₂.Heights.LengthCutGlobal
theorem _root_.solution {y : C} (hy : y ∉ P) (n : ℕ) (v : Fin n → C ⧸ P) (h : y • v = 0) :
    v = 0 := by
  funext i
  have hi := congrFun h i
  rw [Pi.smul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Pi.zero_apply] at hi
  exact (mul_eq_zero.1 hi).resolve_left (fun h => hy (Ideal.Quotient.eq_zero_iff_mem.1 h))
end GroundTheory.Heights₂.Heights.LengthCutGlobal
