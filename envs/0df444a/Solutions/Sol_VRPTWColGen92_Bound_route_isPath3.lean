-- Prove2me | solution 1 for VRPTWColGen92.Bound.route_isPath3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:42:28.633774+00:00
-- url     : https://prove2.me/submissions/3e5b01b6-6208-427f-b195-3f8457c390e9

import Mathlib
import Definitions.Def_VRPTWColGen92_Bound_Network

set_option autoImplicit false
open VRPTWColGen92.Bound

theorem solution {n : ℕ} (I : Instance n) (p : List (Fin (n + 1))) :
    (IsRoute I p → IsPath3 I p) ∧ (IsPath3 I p → IsPath I p) := by
  refine ⟨fun ⟨hpath, hnd⟩ => ⟨hpath, ?_⟩, fun h => h.1⟩
  intro k hk h
  have := (List.Nodup.getElem_inj_iff hnd).1 h
  omega
