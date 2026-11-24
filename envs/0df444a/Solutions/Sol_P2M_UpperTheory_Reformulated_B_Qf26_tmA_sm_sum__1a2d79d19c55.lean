-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qf26_tmA_sm_sum__1a2d79d19c55
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:31.146548+00:00
-- url     : https://prove2.me/submissions/123df7a8-31d2-4db1-bbd0-37ddab9edae6

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TmASmSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qf26.tmA_sm_sum
theorem _root_.solution.{u_1} :
    ∀ {n : Nat} {ε : Fin n → Bool} {ι : Type u_1} (s : Finset ι) (F : ι → Matrix (Fin n) (Fin n) Complex → Complex),
      (∀ (i : ι),
          @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) s i →
            @UpperTheory.Reformulated.B.Qf26.SmoothOnG n ε (F i)) →
        @UpperTheory.Reformulated.B.Qf26.SmoothOnG n ε fun (x : Matrix (Fin n) (Fin n) Complex) ↦ ∑ i ∈ s, F i x := by
  intro n ε ι s F h g₀ hg
  classical
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
  choose! U G hUo hUm hG hE using fun i hi => h i hi g₀ hg
  refine ⟨⋂ i ∈ s, U i, fun x => ∑ i ∈ s, G i x, isOpen_biInter_finset hUo, ?_, ?_, ?_⟩
  · exact Set.mem_iInter₂.2 hUm
  · exact ContDiffOn.sum fun i hi => (hG i hi).mono (Set.biInter_subset_of_mem hi)
  · intro g hgU hgJ
    exact Finset.sum_congr rfl fun i hi => hE i hi g (Set.mem_iInter₂.1 hgU i hi) hgJ
end UpperTheory.Reformulated.B.Qf26.tmA_sm_sum
