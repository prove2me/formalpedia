-- Prove2me | solution 1 for ULHC.stripScan_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:57:29.401521+00:00
-- url     : https://prove2.me/submissions/5989178e-55b4-4a2a-ab98-dabb8493cad1

import Definitions.Def_ULHC_CrPath
import Definitions.Def_ULHC_Comp
import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_Enum
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
open Finset
variable (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side)
variable {V F c s}
namespace ULHC
theorem _root_.solution {n : ℕ}
    (hn : ∀ i < n, IsCell V (cellJ c s i) ∧ LatOK F c s i ∧
      (front (cellJ c s i) s ∈ F ↔ (i % 2 = 1 ↔ i + 1 < n))) :
    ∀ k j, j < n → n ≤ j + k → stripScan V F c s k j = some n := by
  intro k
  induction k with
  | zero => intro j hj hk; omega
  | succ k ih =>
    intro j hj hk
    obtain ⟨hc, hl, hf⟩ := hn j hj
    simp only [stripScan, if_pos (And.intro hc hl)]
    by_cases hj1 : j + 1 = n
    · rw [if_pos (by rw [hf]; omega)]; rw [hj1]
    · rw [if_neg (by rw [hf]; omega)]
      exact ih (j + 1) (by omega) (by omega)
end ULHC
