-- Prove2me | solution 1 for Psi.dyck_none_rest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:48:52.373998+00:00
-- url     : https://prove2.me/submissions/05b47374-37be-4876-95f3-6d755d1437b0

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_cUDraw_prefix
import Theorems.Thm_Psi_fUD_drop_last
import Theorems.Thm_Psi_dyck_leading
import Theorems.Thm_Psi_noDD_high
import Theorems.Thm_Psi_hasDD_of_none
import Theorems.Thm_Psi_cUDraw_fUD_append
import Theorems.Thm_Psi_hasDD_cons
import Theorems.Thm_Psi_isDyckAux_iff
import Theorems.Thm_Psi_runHeight_append
import Theorems.Thm_Psi_runHeight_flatten_UD
import Theorems.Thm_Psi_validFrom_append


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (π : List Bool) (hd : IsDyck π) (hne : π ≠ [])
    (hnone : firstDDidx (π.drop (2 * cUD π + 1)) = none) :
    π.drop (2 * cUD π + 1) = [false] := by
  set c := cUDraw π with hc
  by_cases hcap : 2 * c = π.length
  · have hcge : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h0 | hp
      · exfalso; rw [h0] at hcap; simp at hcap; exact hne (List.eq_nil_of_length_eq_zero hcap.symm)
      · exact hp
    have hcUD : cUD π = c - 1 := by rw [cUD, ← hc, if_pos hcap]
    have hπ : π = (List.replicate c [true, false]).flatten := by
      conv_lhs => rw [cUDraw_prefix π]
      rw [List.drop_eq_nil_of_le (by rw [hcap]), List.append_nil]
    rw [hcUD, hπ, show 2 * (c - 1) + 1 = 2 * c - 1 from by omega, fUD_drop_last c hcge]
  · exfalso
    have hcUD : cUD π = c := by rw [cUD, ← hc, if_neg hcap]
    have hlead := dyck_leading π hd hne
    rw [hcUD] at hlead hnone
    set rest := π.drop (2 * c + 1) with hrestdef
    have hddrest : hasDD rest = false := hasDD_of_none rest hnone
    have hvhe : validFrom rest 1 ∧ runHeight rest 1 = 0 := by
      have hdd2 := hd; rw [IsDyck, isDyckAux_iff] at hdd2; obtain ⟨hv, he⟩ := hdd2
      rw [hlead, validFrom_append, runHeight_flatten_UD] at hv
      rw [hlead, runHeight_append, runHeight_flatten_UD] at he
      exact ⟨by simpa [validFrom] using hv.2, by simpa [runHeight] using he⟩
    have hrestne : rest ≠ [] := by intro h0; rw [h0] at hvhe; simp [runHeight] at hvhe
    obtain ⟨y, r, hyr⟩ := List.exists_cons_of_ne_nil hrestne
    have hy : y = true := by
      by_contra hyf; simp only [Bool.not_eq_true] at hyf; subst hyf
      have hcount : cUDraw π = c + 1 + cUDraw r := by
        conv_lhs => rw [hlead, hyr]
        rw [show (List.replicate c [true, false]).flatten ++ true :: false :: r
            = (List.replicate (c + 1) [true, false]).flatten ++ r from by
            rw [List.replicate_add]; simp [List.flatten_append], cUDraw_fUD_append]
      rw [← hc] at hcount; omega
    subst hy
    rw [hyr] at hvhe hddrest
    refine noDD_high r.length r 2 rfl (by norm_num) ?_ ?_ ?_
    · simpa [validFrom] using hvhe.1
    · simpa [runHeight] using hvhe.2
    · rw [hasDD_cons] at hddrest; simpa using hddrest
end Psi
