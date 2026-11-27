-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmIMultilin_proof_fab781e67397
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:01:30.098594+00:00
-- url     : https://prove2.me/submissions/80eab61d-bc62-404e-980a-cfb927f0a8b5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmIMultilin
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIMultilin_smooth_update_18a1a8380b3d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIMultilin_update_comp_swap_7f6a686cf33e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isSmoothHerm_tensor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
namespace GroundTheory.Heights₂.Heights.Inter
namespace ThmIMultilin
theorem _root_.solution (hS : ThmISymm.Statement) : ThmIMultilin.Statement := by
  intro K _ ι _ I hR P n L j A B hP hL hA hB
  cases n with
  | zero => exact j.elim0
  | succ m =>
    have hAB : IsSmoothHerm (A.tensor B) := isSmoothHerm_tensor hA hB
    have e : ∀ X : HermLine ι, IsSmoothHerm X →
        I P (m + 1) (Function.update L j X) =
          I P (m + 1) (Fin.snoc (fun i : Fin m => L (Equiv.swap j (Fin.last m) i.castSucc)) X) := by
      intro X hX
      rw [← ThmIMultilin.update_comp_swap]
      exact (hS K ι I hR P (m + 1) _ _ hP (ThmIMultilin.smooth_update hL j hX)).symm
    have hM : ∀ i : Fin m, IsSmoothHerm (L (Equiv.swap j (Fin.last m) i.castSucc)) := fun i => hL _
    rw [e _ hAB, e A hA, e B hB]
    exact hR.1 P m _ A B hP hM hA hB
end ThmIMultilin
end GroundTheory.Heights₂.Heights.Inter
