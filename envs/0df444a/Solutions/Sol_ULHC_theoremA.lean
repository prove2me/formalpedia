-- Prove2me | solution 1 for ULHC.theoremA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:20:38.471853+00:00
-- url     : https://prove2.me/submissions/c77ffa5a-3add-4495-8b58-3abc6b961fc3

import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_TheoremA
import Theorems.Thm_ULHC_deg2_flipCol
import Theorems.Thm_ULHC_even_strip_count
import Theorems.Thm_ULHC_seq_count
import Theorems.Thm_ULHC_typeIII_strip
import Theorems.Thm_ULHC_one_strip

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {H : Finset Edge} (hs : Solid V) (hH : Deg2 V H)
    (hHam : ncomp V H = 1) (F : Finset Edge) (hF : Deg2 V F) (h2 : 2 ≤ ncomp V F) :
    ∃ L : List StripSpec, ValidSeq V F L ∧ ncomp V (applySeq F L) + 1 = ncomp V F := by
  suffices h : ∀ m (F : Finset Edge), mu V F H = m → Deg2 V F → 2 ≤ ncomp V F →
      ∃ L : List StripSpec, ValidSeq V F L by
    obtain ⟨L, hL⟩ := h _ F rfl hF h2
    exact ⟨L, hL, seq_count L F hF hL⟩
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro F hm hF h2
  by_cases hT : NoTypeIII V F
  · obtain ⟨σ, hv, hn, hmu⟩ := one_strip hs hH hHam hF hT h2
    rcases Nat.mod_two_eq_zero_or_one σ.n with hev | hodd
    · have hF' := deg2_flipCol σ.n F hF hv.2.1 hv.2.2.1
      have hc := even_strip_count hF hT hv hev
      obtain ⟨L', hL'⟩ := ih (mu V (applyS F σ) H) (by omega) (applyS F σ) rfl hF' (by omega)
      rcases L' with _ | ⟨τ, L'⟩
      · exact hL'.elim
      · exact ⟨σ :: τ :: L', hv, hev, hT, hL'⟩
    · exact ⟨[σ], hv, hodd⟩
  · obtain ⟨σ, hv, hodd⟩ := typeIII_strip hT
    exact ⟨[σ], hv, hodd⟩
end ULHC
