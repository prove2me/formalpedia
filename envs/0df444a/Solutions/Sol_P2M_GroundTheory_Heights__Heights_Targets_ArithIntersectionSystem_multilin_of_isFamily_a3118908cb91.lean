-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ArithIntersectionSystem_multilin_of_isFamily_a3118908cb91
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:21:04.354952+00:00
-- url     : https://prove2.me/submissions/34602fcf-f23e-478d-b507-eb559b4b70ba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmIMultilin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ArithSystem
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Targets.ArithIntersectionSystem
namespace GroundTheory.Heights₂.Heights.Targets.ArithIntersectionSystem
theorem _root_.solution {I : AllFam} (hI : I.IsFamily) : IsMultilinFam I := by
  intro K _ ι _ P n L j A B hP hL hA hB
  cases n with
  | zero => exact j.elim0
  | succ m =>
    obtain ⟨hsym, hadd, -⟩ := hI K ι
    have e : ∀ X : HermLine ι, IsSmoothHerm X →
        I K ι P (m + 1) (Function.update L j X) =
          I K ι P (m + 1)
            (Fin.snoc (fun i : Fin m => L (Equiv.swap j (Fin.last m) i.castSucc)) X) := by
      intro X hX
      rw [← GroundTheory.Heights₂.Heights.Inter.ThmIMultilin.update_comp_swap]
      exact (hsym P (m + 1) _ _ hP
        (GroundTheory.Heights₂.Heights.Inter.ThmIMultilin.smooth_update hL j hX)).symm
    rw [e _ (isSmoothHerm_tensor hA hB), e A hA, e B hB]
    exact hadd P m _ A B hP (fun i => hL _) hA hB
end GroundTheory.Heights₂.Heights.Targets.ArithIntersectionSystem
