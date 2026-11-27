-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_SummandLocalization_aux1__79632e0fedfc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:15:13.734248+00:00
-- url     : https://prove2.me/submissions/8571b888-de27-4aa4-895f-f4f8f33a871d

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

namespace UpperTheory.Reformulated.B.SummandLocalization.aux1
theorem _root_.solution.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) {x y : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → x + y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  rintro R _ W _ _ S L x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
  refine ⟨s * t, S.mul_mem hs ht, ?_⟩
  rw [smul_add, mul_smul s t y, mul_comm s t, mul_smul t s x]
  exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)
end UpperTheory.Reformulated.B.SummandLocalization.aux1
