-- Prove2me | solution 1 for ResourceScheduling.Graph.block_laws
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:01:42.014059+00:00
-- url     : https://prove2.me/submissions/5e7a7ec0-31ee-47e6-8f57-b206f9cf6644

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
import Theorems.Thm_ResourceScheduling_Graph_ram_safe_laws

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg GraphProgram

theorem solution (ps qs : List Code) (B : ℕ) (s : RAMState GraphReg) :
    (block (ps ++ qs)).eval s = (block qs).eval ((block ps).eval s) ∧
    (RAMSafe (block ps) B s → RAMSafe (block qs) B ((block ps).eval s) →
      RAMSafe (block (ps ++ qs)) B s) := by
  induction ps generalizing s with
  | nil => exact ⟨rfl, fun _ h => h⟩
  | cons p ps ih =>
    obtain ⟨he,hs⟩ := ih (p.eval s)
    refine ⟨he, ?_⟩
    intro hp hq
    have htail : RAMSafe (block ps) B (p.eval s) := ⟨hp.1.2, hp.2⟩
    have hr := hs htail hq
    exact ⟨⟨hp.1.1,hr.1⟩,hr.2⟩

#print axioms solution
