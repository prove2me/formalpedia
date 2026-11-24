-- Prove2me | solution 1 for ULHC.walkCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:24:48.343903+00:00
-- url     : https://prove2.me/submissions/668d8bbc-6729-4e1c-8fc1-c4c99aebd34a

import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_CostTwoFactor
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset TF
namespace ULHC
theorem _root_.solution (V : Finset Pt) (F0 : Finset Edge) :
    ∀ (Ls : List (Finset Pt)) (v : Pt) (F : Finset Edge), walkCost V F0 Ls v F ≤ 45 * (Ls.length + 1)
  | [], _, _ => by simp [walkCost]
  | L :: Ls, v, F => by
    simp only [walkCost, List.length_cons]
    by_cases hv : v ∈ L
    · rw [if_pos hv]; have := solution V F0 Ls v F; omega
    · rw [if_neg hv]
      rcases pred V F0 L v with _ | e
      · simp only; unfold predCost; omega
      · simp only
        have := solution V F0 Ls (other e v) (if Black v then F.erase e else insert e F)
        unfold predCost; omega
end ULHC
