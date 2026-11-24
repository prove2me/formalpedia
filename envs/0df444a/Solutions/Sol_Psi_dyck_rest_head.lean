-- Prove2me | solution 1 for Psi.dyck_rest_head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:48:16.873854+00:00
-- url     : https://prove2.me/submissions/c02eb049-ba50-4e9e-8ee9-823323dafa39

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_cUDraw_prefix
import Theorems.Thm_Psi_fUD_drop_last
import Theorems.Thm_Psi_dyck_leading
import Theorems.Thm_Psi_cUDraw_fUD_append


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (π : List Bool) (i : ℕ) (hd : IsDyck π) (hne : π ≠ [])
    (hsome : firstDDidx (π.drop (2 * cUD π + 1)) = some i) :
    (π.drop (2 * cUD π + 1)).head? = some true := by
  set c := cUDraw π with hc
  have hncap : 2 * c ≠ π.length := by
    intro hcap
    have hcge : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h0 | hp
      · exfalso; rw [h0] at hcap; simp at hcap; exact hne (List.eq_nil_of_length_eq_zero hcap.symm)
      · exact hp
    have hπ : π = (List.replicate c [true, false]).flatten := by
      conv_lhs => rw [cUDraw_prefix π]
      rw [List.drop_eq_nil_of_le (by rw [hcap]), List.append_nil]
    have hcUD : cUD π = c - 1 := by rw [cUD, ← hc, if_pos hcap]
    have hrf : π.drop (2 * cUD π + 1) = [false] := by
      rw [hcUD, hπ, show 2 * (c - 1) + 1 = 2 * c - 1 from by omega, fUD_drop_last c hcge]
    rw [hrf] at hsome; simp [firstDDidx] at hsome
  have hcUD : cUD π = c := by rw [cUD, ← hc, if_neg hncap]
  set rest := π.drop (2 * cUD π + 1) with hrest
  have hrestne : rest ≠ [] := by intro hh; rw [hh] at hsome; simp [firstDDidx] at hsome
  by_contra hcon
  obtain ⟨x, xs, hxs⟩ := List.exists_cons_of_ne_nil hrestne
  have hx : x = false := by
    rw [hxs] at hcon; simp only [List.head?_cons] at hcon
    cases x with | true => exact absurd rfl hcon | false => rfl
  subst hx
  have hlead := dyck_leading π hd hne
  rw [← hrest, hxs] at hlead
  have hcount : cUDraw π = cUD π + 1 + cUDraw xs := by
    conv_lhs => rw [hlead]
    rw [show (List.replicate (cUD π) [true,false]).flatten ++ true :: false :: xs
        = (List.replicate (cUD π) [true,false]).flatten ++ ([true,false] ++ xs) from rfl,
      ← List.append_assoc,
      show (List.replicate (cUD π) [true,false]).flatten ++ [true,false]
        = (List.replicate (cUD π + 1) [true,false]).flatten from by
        rw [List.replicate_add]; simp [List.flatten_append],
      cUDraw_fUD_append]
  rw [← hc, hcUD] at hcount; omega
end Psi
