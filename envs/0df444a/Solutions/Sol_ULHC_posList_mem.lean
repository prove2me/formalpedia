-- Prove2me | solution 1 for ULHC.posList_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:10:29.674882+00:00
-- url     : https://prove2.me/submissions/37ea6df1-1435-403f-8dad-80fd7c558fc4

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution : ∀ (L : List StripSpec) (k : ℕ), k ≤ 3 → ∀ x ∈ posList k L,
    x.σ ∈ L ∧ k ≤ x.pos ∧ x.pos ≤ 3
  | [], _, _, x, hx => by simp [posList] at hx
  | σ :: L, k, hk, x, hx => by
    rw [posList, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨by simp, le_refl _, hk⟩
    · obtain ⟨h1, h2, h3⟩ := solution L (min (k + 1) 3) (min_le_right _ _) x hx
      exact ⟨List.mem_cons_of_mem _ h1, by omega, h3⟩
end ULHC
