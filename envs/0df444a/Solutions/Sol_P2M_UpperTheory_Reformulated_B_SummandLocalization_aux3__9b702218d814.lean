-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_SummandLocalization_aux3__9b702218d814
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:15:23.211709+00:00
-- url     : https://prove2.me/submissions/b52d4a37-a136-4bc6-802c-25ed5c3a42d9

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

namespace UpperTheory.Reformulated.B.SummandLocalization.aux3
theorem _root_.solution.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) (r : R) {x : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → r • x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  rintro R _ W _ _ S L r x ⟨s, hs, hx⟩
  refine ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact L.smul_mem r hx
end UpperTheory.Reformulated.B.SummandLocalization.aux3
