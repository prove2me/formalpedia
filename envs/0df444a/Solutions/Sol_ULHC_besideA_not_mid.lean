-- Prove2me | solution 1 for ULHC.besideA_not_mid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:02:27.54243+00:00
-- url     : https://prove2.me/submissions/5335ad7a-f97e-4b44-8829-870a55aef461

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
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
theorem _root_.solution (c : Pt) (s : Side) (k : ℕ) {tf : Side} (ht : tf = s ∨ tf = s.opp) :
    ¬ IsMid c s k (back1 (nb (cellJ c s (k + 1)) (latA s)) tf) ∧
      ¬ IsMid c s k (front1 (nb (cellJ c s (k + 1)) (latA s)) tf) := by
  obtain ⟨p, q⟩ := c
  rcases ht with h0 | h0 <;> rw [h0] <;> constructor <;> rintro ⟨j, hj, hjk, h⟩ <;> cases s <;>
    simp [back1, front1, front2, nb, latA, cellJ, Side.opp] at h <;> omega
end ULHC
