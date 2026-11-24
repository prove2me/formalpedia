-- Prove2me | solution 1 for ULHC.deg2_flipCol
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:40.098172+00:00
-- url     : https://prove2.me/submissions/af67d761-6eda-4872-9c76-8775299eedee

import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_TheoremA
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_back_cellJ_succ
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_flipCol_succ
import Theorems.Thm_ULHC_mkBF_cellE
import Theorems.Thm_ULHC_mkLat_cellE
import Theorems.Thm_ULHC_pat_flip_end
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {c : Pt} {s : Side} :
    ∀ n (F : Finset Edge), Deg2 V F → StripPat F c s n → (∀ j < n, IsCell V (cellJ c s j)) →
      Deg2 V (flipCol F c s n) := by
  intro n
  induction n with
  | zero => intro F hF _ _; exact hF
  | succ n ih =>
    intro F hF hpat hcell
    rw [flipCol_succ]
    have hce := hcell n (by omega)
    obtain ⟨hb, hl, hf⟩ := hpat
    have mF : front (cellJ c s n) s ∈ F ↔ n % 2 = 0 := by
      have := hf n (by omega); simp only [lt_self_iff_false, iff_false] at this; rw [this]; omega
    have mB : back (cellJ c s n) s ∈ F ↔ n % 2 = 0 := by
      rcases n with _ | n
      · simp only [cellJ_zero]; simp [hb]
      · rw [back_cellJ_succ]
        have := hf n (by omega)
        have q : n + 1 < n + 1 + 1 := by omega
        simp only [q, iff_true] at this
        rw [this]; omega
    have mL1 := (hl n (by omega)).1
    have mL2 := (hl n (by omega)).2
    have hF' : Deg2 V (ULHC.flip F (cellJ c s n)) := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · exact hF.flip (mkBF _ s) hce (mkBF_cellE _ s) (mB.2 h) (mF.2 h)
          (fun h' => by have := mL1.1 h'; omega) (fun h' => by have := mL2.1 h'; omega)
      · exact hF.flip (mkLat _ s) hce (mkLat_cellE _ s) (mL1.2 h) (mL2.2 h)
          (fun h' => by have := mB.1 h'; omega) (fun h' => by have := mF.1 h'; omega)
    rcases n with _ | n
    · simpa [flipCol] using hF'
    · exact ih _ hF' (pat_flip_end ⟨hb, hl, hf⟩) (fun j hj => hcell j (by omega))
end ULHC
