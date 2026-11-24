-- Prove2me | solution 1 for Psi.phi_psi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:55:27.563826+00:00
-- url     : https://prove2.me/submissions/700f953c-561b-4a2c-9146-de0222dedd1e

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_dyck_leading
import Theorems.Thm_Psi_dyck_none_rest
import Theorems.Thm_Psi_phi_psi_some
import Theorems.Thm_Psi_noDescent_sorted


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (π : List Bool) (h : IsDyck π) (hne : π ≠ []) :
    phiPath (psiPath π).1 (psiPath π).2 = π := by
  suffices H : ∀ n, ∀ π : List Bool, π.length = n → IsDyck π → π ≠ [] →
      phiPath (psiPath π).1 (psiPath π).2 = π by exact H π.length π rfl h hne
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro π hlen hd hne
    rcases hfd : firstDDidx (π.drop (2 * cUD π + 1)) with _ | i
    · have hrf : π.drop (2 * cUD π + 1) = [false] := dyck_none_rest π hd hne hfd
      have hpsi : psiPath π = (List.replicate (cUD π) false, [0]) := by rw [psiPath.eq_1, hfd]
      rw [hpsi]
      conv_rhs => rw [dyck_leading π hd hne, hrf]
      rw [phiPath.eq_1, if_pos (by simpa using noDescent_sorted (cUD π) 0)]
      simp [List.append_assoc]
    · exact phi_psi_some n IH π hlen hd hne i hfd
end Psi
