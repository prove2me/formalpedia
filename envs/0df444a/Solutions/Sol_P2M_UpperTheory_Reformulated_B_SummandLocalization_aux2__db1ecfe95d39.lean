-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_SummandLocalization_aux2__db1ecfe95d39
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:15:18.4528+00:00
-- url     : https://prove2.me/submissions/33606be8-d67c-400c-bc8b-f2f32fae6474

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SummandLocalization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.SummandLocalization.aux2
theorem _root_.solution.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] {W : Type u_2} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W), ∃ s ∈ S, s • (0 : W) ∈ L := by
  intro R _ W _ _ S L
  exact ⟨1, S.one_mem, by rw [smul_zero]; exact L.zero_mem⟩
end UpperTheory.Reformulated.B.SummandLocalization.aux2
