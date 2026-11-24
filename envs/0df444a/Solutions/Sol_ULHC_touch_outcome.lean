-- Prove2me | solution 1 for ULHC.touch_outcome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:27:19.400055+00:00
-- url     : https://prove2.me/submissions/c3576638-09ea-4414-ad15-5042f01154a6

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
import Theorems.Thm_ULHC_cellJ_down
import Theorems.Thm_ULHC_behind_up
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_beside_end1
import Theorems.Thm_ULHC_beside_end2
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_outer1_body
import Theorems.Thm_ULHC_outer2_body
import Theorems.Thm_ULHC_reach_end
import Theorems.Thm_ULHC_side1_down
import Theorems.Thm_ULHC_side2_down
import Theorems.Thm_ULHC_side_chain1
import Theorems.Thm_ULHC_side_chain2
import Theorems.Thm_ULHC_sig_of_pat
import Theorems.Thm_ULHC_touch_behind
import Theorems.Thm_ULHC_touch_cases
import Theorems.Thm_ULHC_touch_side1_end
import Theorems.Thm_ULHC_touch_side2_end


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIII V (flipCol F c s (k + 2)))
  {z : Pt} {tf : Side} {m : ℕ} (hz : StripPat F z tf m)
include hs x0 hconn hF hT hk hcell hpat hsep hT' hz
omit hs hconn
omit x0
namespace ULHC
theorem _root_.solution {i j : ℕ} (hi : i < m) (hj : j < k + 2) {x : Edge}
    (hx1 : x ∈ cellE (cellJ z tf i)) (hx2 : x ∈ cellE (cellJ c s j)) :
    (∃ i' < m, cellJ z tf i' = cellJ c s (k + 1)) ∨
      (∃ i' < m, cellJ z tf i' = nb (cellJ c s (k + 1)) s) ∨
      (tf = s.opp ∧ ∃ i0 < m, i0 % 2 = 0 ∧
        (cellJ z tf i0 = nb c (latA s) ∨ cellJ z tf i0 = nb c (latB s))) := by
  have re : ∀ i' j', i' < m → j' ≤ k + 1 → cellJ z tf i' = cellJ c s j' →
      ∃ i'' < m, cellJ z tf i'' = cellJ c s (k + 1) := fun i' j' hi' hj' hq => by
    obtain ⟨i'', -, h1, h2⟩ := reach_end hk hpat (sig_of_pat hz) (k + 1 - j') i' j' (by omega) (Nat.zero_le _) hi' hq
    exact ⟨i'', h1, h2⟩
  rcases touch_cases s hx1 hx2 with hq | hq | hq | hq | hq
  · exact Or.inl (re i j hi (by omega) hq)
  · by_cases hjk : j ≤ k
    · exact Or.inl (re i (j + 1) hi (by omega) (by rw [hq, nb_cellJ]))
    · exact Or.inr (Or.inl ⟨i, hi, by rw [hq, show j = k + 1 by omega]⟩)
  · rcases j with _ | j
    · rw [cellJ_zero] at hq
      obtain ⟨ht, _, hi1⟩ := touch_behind hF hT hk hcell hpat hsep (sig_of_pat hz) (Nat.zero_le _) hi hq
      refine Or.inl (re (i + 1) 0 hi1 (by omega) ?_)
      rw [← nb_cellJ, hq, ht, behind_up, cellJ_zero]
    · exact Or.inl (re i j hi (by omega) (by rw [hq, cellJ_down]))
  · by_cases hjk : j ≤ k
    · obtain ⟨ht, i0, -, h1, h2, h3⟩ := side_chain1 hF hT hk hcell hpat hsep (sig_of_pat hz) j i hjk (Nat.zero_le _) hi hq
      exact Or.inr (Or.inr ⟨ht, i0, h1, h2, Or.inl h3⟩)
    · obtain rfl : j = k + 1 := by omega
      rcases touch_side1_end hF hk hcell hpat (sig_of_pat hz) (Nat.zero_le _) hi hq with ⟨ht, _, hi1⟩ | ⟨_, hf, hl⟩
      · obtain ⟨ht', i0, -, h1, h2, h3⟩ := side_chain1 hF hT hk hcell hpat hsep (sig_of_pat hz) k (i + 1) le_rfl (Nat.zero_le _)
          hi1 (by rw [← nb_cellJ, hq, ht, side1_down])
        exact Or.inr (Or.inr ⟨ht', i0, h1, h2, Or.inl h3⟩)
      · exact absurd hT' (beside_end1 hF hT hk hcell hpat hsep
          ((outer1_body hF hcell hpat le_rfl).2 hk) hf hl)
  · by_cases hjk : j ≤ k
    · obtain ⟨ht, i0, -, h1, h2, h3⟩ := side_chain2 hF hT hk hcell hpat hsep (sig_of_pat hz) j i hjk (Nat.zero_le _) hi hq
      exact Or.inr (Or.inr ⟨ht, i0, h1, h2, Or.inr h3⟩)
    · obtain rfl : j = k + 1 := by omega
      rcases touch_side2_end hF hk hcell hpat (sig_of_pat hz) (Nat.zero_le _) hi hq with ⟨ht, _, hi1⟩ | ⟨_, hf, hl⟩
      · obtain ⟨ht', i0, -, h1, h2, h3⟩ := side_chain2 hF hT hk hcell hpat hsep (sig_of_pat hz) k (i + 1) le_rfl (Nat.zero_le _)
          hi1 (by rw [← nb_cellJ, hq, ht, side2_down])
        exact Or.inr (Or.inr ⟨ht', i0, h1, h2, Or.inr h3⟩)
      · exact absurd hT' (beside_end2 hF hT hk hcell hpat hsep
          ((outer2_body hF hcell hpat le_rfl).2 hk) hf hl)
end ULHC
