-- Prove2me | solution 1 for ULHC.DStep.light
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:43:56.347129+00:00
-- url     : https://prove2.me/submissions/9e9d41ae-628c-420b-99ec-ea58013ebcb9

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual

set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
namespace DStep
theorem _root_.solution {a d : Pt} {E : Finset Edge} (h : DStep V F a d E) : ∀ e ∈ E, e ∉ F := by
  cases h with
  | inner tf _ _ hl => intro e he; rw [Finset.mem_singleton.1 he]; exact hl
  | outer c' tf t' _ _ _ _ hl hl' =>
    intro e he
    rcases Finset.mem_symmDiff.1 he with ⟨h, _⟩ | ⟨h, _⟩
    · rw [Finset.mem_singleton.1 h]; exact hl
    · rw [Finset.mem_singleton.1 h]; exact hl'
end DStep
end ULHC
