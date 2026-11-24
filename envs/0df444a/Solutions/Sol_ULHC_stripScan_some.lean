-- Prove2me | solution 1 for ULHC.stripScan_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:57:15.637806+00:00
-- url     : https://prove2.me/submissions/b44735d7-5adb-425a-803c-7d8fb0aec5ce

import Definitions.Def_ULHC_CrPath
import Definitions.Def_ULHC_Comp
import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_Enum
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
variable (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side)
variable {V F c s}
namespace ULHC
theorem _root_.solution {k j m : ℕ} (h : stripScan V F c s k j = some m) :
    j < m ∧ ∀ i, j ≤ i → i < m → IsCell V (cellJ c s i) ∧ LatOK F c s i ∧
      (front (cellJ c s i) s ∈ F ↔ (i % 2 = 1 ↔ i + 1 < m)) := by
  induction k generalizing j with
  | zero => simp [stripScan] at h
  | succ k ih =>
    simp only [stripScan] at h
    split_ifs at h with h1 h2
    · cases h
      refine ⟨by omega, fun i hi hi' => ?_⟩
      obtain rfl : i = j := by omega
      refine ⟨h1.1, h1.2, ?_⟩
      rw [h2]; omega
    · obtain ⟨hjm, hrest⟩ := ih h
      refine ⟨by omega, fun i hi hi' => ?_⟩
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt
      · refine ⟨h1.1, h1.2, ?_⟩
        have hr : (j % 2 = 1 ↔ j + 1 < m) ↔ j % 2 = 1 :=
          ⟨fun h => h.2 (by omega), fun h => ⟨fun _ => by omega, fun _ => h⟩⟩
        rw [hr]
        by_cases hf : front (cellJ c s j) s ∈ F
        · simp only [hf, true_iff] at h2 ⊢; omega
        · simp only [hf, false_iff] at h2 ⊢; omega
      · exact hrest i (by omega) hi'
end ULHC
