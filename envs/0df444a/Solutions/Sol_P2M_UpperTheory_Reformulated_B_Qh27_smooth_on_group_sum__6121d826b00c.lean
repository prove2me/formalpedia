-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qh27_smooth_on_group_sum__6121d826b00c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:37.85567+00:00
-- url     : https://prove2.me/submissions/92336032-e3ff-4dd6-8630-45ddd7ddb741

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnGroupSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qh27.smooth_on_group_sum
theorem _root_.solution.{u_1} :
    ∀ {n : Nat} {ε : Fin n → Bool} {ι : Type u_1} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) Complex → Complex),
      (∀ (i : ι),
          @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) s i →
            @UpperTheory.Reformulated.B.Qh27.SmoothOnG n ε (f i)) →
        @UpperTheory.Reformulated.B.Qh27.SmoothOnG n ε fun (x : Matrix (Fin n) (Fin n) Complex) ↦ ∑ i ∈ s, f i x := by
  intro n ε ι s f h g₀ hg₀
  letI := @Matrix.normedAddCommGroup (Fin n) (Fin n) Complex _ _ _
  letI := @Matrix.normedSpace Real (Fin n) (Fin n) Complex _ _ _ _ _
  choose! U F hU hmem hF heq using fun i hi ↦ h i hi g₀ hg₀
  refine ⟨⋂ i ∈ s, U i, fun x ↦ ∑ i ∈ s, F i x, isOpen_biInter_finset hU,
    Set.mem_iInter₂.2 hmem, ?_, ?_⟩
  · exact ContDiffOn.sum fun i hi ↦ (hF i hi).mono (Set.biInter_subset_of_mem (Finset.mem_coe.2 hi))
  · intro g hg hgu
    exact Finset.sum_congr rfl fun i hi ↦ heq i hi g (Set.mem_iInter₂.1 hg i hi) hgu
end UpperTheory.Reformulated.B.Qh27.smooth_on_group_sum
