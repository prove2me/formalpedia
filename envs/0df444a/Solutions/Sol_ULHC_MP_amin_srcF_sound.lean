-- Prove2me | solution 1 for ULHC.MP.amin_srcF_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:52:02.821287+00:00
-- url     : https://prove2.me/submissions/edeac047-ac07-4334-b339-7d9469552ec1

import Mathlib
import Definitions.Def_ULHC_MinPath
import Theorems.Thm_ULHC_MP_amin_mem
import Theorems.Thm_ULHC_MP_B_sound

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable [DecidableEq α]
variable (NL : List α) (src mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
namespace ULHC.MP
theorem _root_.solution {r : ℕ × List α}
    (h : amin (srcF NL src mid tgt edge w) NL = some r) :
    r.1 = pw w r.2 ∧ IsPath src mid tgt edge r.2 ∧ ∀ z ∈ r.2, z ∈ NL := by
  obtain ⟨x, -, hx⟩ := amin_mem h
  unfold srcF at hx
  by_cases hs : src x = true
  · rw [if_pos hs] at hx
    obtain ⟨h1, L, h2, h3, h4, -⟩ := B_sound NL mid tgt edge w NL.length x r hx
    refine ⟨h1, ?_, h4⟩
    rw [h2]
    exact ⟨hs, h3⟩
  · rw [if_neg hs] at hx
    cases hx
end ULHC.MP
