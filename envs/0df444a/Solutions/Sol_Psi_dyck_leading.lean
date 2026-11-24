-- Prove2me | solution 1 for Psi.dyck_leading
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:46:36.1619+00:00
-- url     : https://prove2.me/submissions/761940d0-05cd-4c45-a1bd-eeabbd6c7b36

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_cUDraw_prefix
import Theorems.Thm_Psi_cUDraw_len
import Theorems.Thm_Psi_fUD_drop_last
import Theorems.Thm_Psi_dyck_drop_fUD
import Theorems.Thm_Psi_dyck_head


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (π : List Bool) (hd : IsDyck π) (hne : π ≠ []) :
    π = (List.replicate (cUD π) [true, false]).flatten ++ true :: π.drop (2 * cUD π + 1) := by
  set c := cUDraw π with hc
  have hpre := cUDraw_prefix π
  have hsuf : IsDyck (π.drop (2 * c)) := dyck_drop_fUD π hd
  by_cases hcap : 2 * c = π.length
  · have hcge : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h0 | hp
      · exfalso; rw [h0] at hcap; simp at hcap; exact hne (List.eq_nil_of_length_eq_zero hcap.symm)
      · exact hp
    have hcUD : cUD π = c - 1 := by rw [cUD, ← hc, if_pos hcap]
    have hπfUD : π = (List.replicate c [true, false]).flatten := by
      conv_lhs => rw [hpre]
      rw [List.drop_eq_nil_of_le (by rw [hcap]), List.append_nil]
    have hsplit : π = (List.replicate (c - 1) [true, false]).flatten ++ [true, false] := by
      rw [hπfUD, show c = (c - 1) + 1 from by omega, List.replicate_add]
      simp [List.flatten_append]
    have hpd : π.drop (2 * (c - 1) + 1) = [false] := by
      rw [hπfUD, show 2 * (c - 1) + 1 = 2 * c - 1 from by omega, fUD_drop_last c hcge]
    rw [hcUD, hpd]; exact hsplit
  · have hcUD : cUD π = c := by rw [cUD, ← hc, if_neg hcap]
    have hdropne : π.drop (2 * c) ≠ [] := by
      intro hnil; rw [List.drop_eq_nil_iff] at hnil; have := cUDraw_len π; omega
    have hhead : (π.drop (2 * c)).head? = some true := dyck_head _ hsuf hdropne
    obtain ⟨r, hr⟩ : ∃ r, π.drop (2 * c) = true :: r := by
      cases hh : π.drop (2 * c) with
      | nil => exact absurd hh hdropne
      | cons x xs => rw [hh] at hhead; simp only [List.head?_cons, Option.some.injEq] at hhead
                     subst hhead; exact ⟨xs, rfl⟩
    rw [hcUD]; conv_lhs => rw [hpre]
    rw [hr]
    have hrr : π.drop (2 * c + 1) = r := by rw [← List.drop_drop, hr]; rfl
    rw [hrr]
end Psi
