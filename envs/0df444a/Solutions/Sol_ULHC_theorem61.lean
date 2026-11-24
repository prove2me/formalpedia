-- Prove2me | solution 1 for ULHC.theorem61
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:23:22.265495+00:00
-- url     : https://prove2.me/submissions/b0b1e028-cf7d-4d4a-ae9b-6d4c29150a15

import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_TheoremA
import Theorems.Thm_ULHC_theoremA
import Theorems.Thm_ULHC_deg2_applySeq
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
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {H : Finset Edge} (hs : Solid V) (hH : Deg2 V H)
    (hHam : ncomp V H = 1) :
    ∀ (F : Finset Edge), Deg2 V F → 1 ≤ ncomp V F →
      ∃ Ls : List (List StripSpec), ValidChain V F Ls ∧ Ls.length + 1 = ncomp V F ∧
        ncomp V (applyChain F Ls) = 1 := by
  suffices h : ∀ k (F : Finset Edge), ncomp V F = k + 1 → Deg2 V F →
      ∃ Ls : List (List StripSpec), ValidChain V F Ls ∧ Ls.length = k ∧
        ncomp V (applyChain F Ls) = 1 by
    intro F hF h1
    obtain ⟨Ls, h1', h2', h3'⟩ := h (ncomp V F - 1) F (by omega) hF
    exact ⟨Ls, h1', by omega, h3'⟩
  intro k
  induction k with
  | zero => intro F hk _; exact ⟨[], trivial, rfl, hk⟩
  | succ k ih =>
    intro F hk hF
    obtain ⟨L, hL, hc⟩ := theoremA hs hH hHam F hF (by omega)
    obtain ⟨Ls, h1, h2, h3⟩ := ih (applySeq F L) (by omega) (deg2_applySeq L F hF hL)
    exact ⟨L :: Ls, ⟨hL, h1⟩, by simp [h2], h3⟩
end ULHC
