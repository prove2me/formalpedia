-- Prove2me | solution 1 for ULHC.MP.amin_srcF_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:52:08.500563+00:00
-- url     : https://prove2.me/submissions/ead2f817-fd4d-4b66-9bdf-8b713480fec7

import Mathlib
import Definitions.Def_ULHC_MinPath
import Theorems.Thm_ULHC_MP_pw_sublist
import Theorems.Thm_ULHC_MP_shortcut
import Theorems.Thm_ULHC_MP_length_le_card
import Theorems.Thm_ULHC_MP_amin_le
import Theorems.Thm_ULHC_MP_B_opt

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable [DecidableEq α]
variable (NL : List α) (src mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
namespace ULHC.MP
theorem _root_.solution {q : List α} (hq : IsPath src mid tgt edge q)
    (hqN : ∀ x ∈ q, x ∈ NL) :
    ∃ r, amin (srcF NL src mid tgt edge w) NL = some r ∧ r.1 ≤ pw w q := by
  cases q with
  | nil => exact hq.elim
  | cons x L =>
    obtain ⟨hs, ht⟩ := hq
    obtain ⟨L', ht', hnd, hsub⟩ := shortcut ht
    have hN' : ∀ z ∈ x :: L', z ∈ NL := fun z hz => hqN z (hsub.subset hz)
    have hlen : L'.length < NL.length := by
      have := length_le_card hnd hN'
      rw [List.length_cons] at this
      omega
    obtain ⟨c, hB, hc⟩ := B_opt NL mid tgt edge w NL.length x L' ht' hN' hlen
    have hf : srcF NL src mid tgt edge w x = some c := by
      unfold srcF
      rw [if_pos hs]
      exact hB
    obtain ⟨r, hr, hr'⟩ := amin_le ((hN' x (by simp))) hf
    exact ⟨r, hr, hr'.trans (hc.trans (pw_sublist hsub))⟩
end ULHC.MP
