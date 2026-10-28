-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_6
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:32:36.669082+00:00
-- url     : https://prove2.me/submissions/81292aa2-30bf-4583-99cb-3d3aa34ef384

import Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_6_chunk_0
import Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_6_chunk_1
import Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_6_chunk_2
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
theorem solution : ∀ m : Fin 60,
    (RHDirect132Integer.gammaRe 6 m.val, RHDirect132Integer.gammaIm 6 m.val) =
      ((TaoFivePrimes_RHDirect132GammaData1.getD 2 []).getD m.val (0,0)) := by
  intro m
  by_cases h0 : m.val<20
  · have h := TaoFivePrimes.rh_direct_132_gamma_panel_6_chunk_0 ⟨m.val,h0⟩
    simpa only [Fin.val_mk, Nat.zero_add] using h
  by_cases h1 : m.val<40
  · have hm : 20 ≤ m.val := by omega
    have h := TaoFivePrimes.rh_direct_132_gamma_panel_6_chunk_1 ⟨m.val-20,by omega⟩
    simpa only [Fin.val_mk, Nat.add_sub_of_le hm] using h
  · have hm : 40 ≤ m.val := by omega
    have h := TaoFivePrimes.rh_direct_132_gamma_panel_6_chunk_2 ⟨m.val-40,by omega⟩
    simpa only [Fin.val_mk, Nat.add_sub_of_le hm] using h
