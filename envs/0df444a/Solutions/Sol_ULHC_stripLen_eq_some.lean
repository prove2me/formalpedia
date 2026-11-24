-- Prove2me | solution 1 for ULHC.stripLen_eq_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:59:38.040049+00:00
-- url     : https://prove2.me/submissions/7d3a1594-0f08-499e-94bd-ccfbe678e922

import Definitions.Def_ULHC_CrPath
import Definitions.Def_ULHC_Comp
import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_Enum
import Theorems.Thm_ULHC_stripScan_some
import Theorems.Thm_ULHC_stripScan_of
import Theorems.Thm_ULHC_strip_len_le
import Theorems.Thm_ULHC_NoTypeIII_at


set_option autoImplicit true
open ULHC
open Finset
variable (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side)
variable {V F c s}
namespace ULHC
theorem _root_.solution {n : ℕ} :
    stripLen V F c s = some n ↔
      1 ≤ n ∧ StripPat F c s n ∧ ∀ j < n, IsCell V (cellJ c s j) := by
  constructor
  · intro h
    unfold stripLen at h
    split_ifs at h with hb
    obtain ⟨h0, hr⟩ := stripScan_some h
    refine ⟨h0, ⟨hb, fun j hj => (hr j (Nat.zero_le _) hj).2.1,
      fun j hj => (hr j (Nat.zero_le _) hj).2.2⟩, fun j hj => (hr j (Nat.zero_le _) hj).1⟩
  · rintro ⟨h1, ⟨hb, hl, hf⟩, hc⟩
    unfold stripLen
    rw [if_pos hb]
    exact stripScan_of (fun i hi => ⟨hc i hi, hl i hi, hf i hi⟩) _ 0 (by omega)
      (by have := strip_len_le hc; omega)
end ULHC
