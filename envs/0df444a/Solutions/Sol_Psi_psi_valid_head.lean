-- Prove2me | solution 1 for Psi.psi_valid_head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:56:24.123303+00:00
-- url     : https://prove2.me/submissions/7ad2731d-b695-4f8f-a517-9a8fa61febaa

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
import Theorems.Thm_Psi_numNBeforeDD_fUD
import Theorems.Thm_Psi_isValid_zeros
import Theorems.Thm_Psi_psi_valid_head_some
import Theorems.Thm_Psi_desComp_noDescent
import Theorems.Thm_Psi_dyck_leading
import Theorems.Thm_Psi_dyck_none_rest
import Theorems.Thm_Psi_noDescent_sorted


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (π : List Bool) (hd : IsDyck π) (hne : π ≠ []) :
    IsValid (psiPath π).1 (psiPath π).2 ∧
      (tauOf (psiPath π).1 (psiPath π).2).headD 0 = numNBeforeDD π := by
  suffices H : ∀ n, ∀ π : List Bool, π.length = n → IsDyck π → π ≠ [] →
      IsValid (psiPath π).1 (psiPath π).2 ∧
        (tauOf (psiPath π).1 (psiPath π).2).headD 0 = numNBeforeDD π by
    exact H π.length π rfl hd hne
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro π hlen hd hne
    rcases hfd : firstDDidx (π.drop (2 * cUD π + 1)) with _ | i
    · have hrf : π.drop (2 * cUD π + 1) = [false] := dyck_none_rest π hd hne hfd
      have hpsi : psiPath π = (List.replicate (cUD π) false, [0]) := by rw [psiPath.eq_1, hfd]
      refine ⟨?_, ?_⟩
      · rw [hpsi]; exact isValid_zeros (cUD π)
      · have h1 : (psiPath π).1 = List.replicate (cUD π) false := by rw [hpsi]
        have h2 : (psiPath π).2 = [0] := by rw [hpsi]
        rw [h1, h2]
        have hrhs : numNBeforeDD π = cUD π + 1 := by
          have hπfud : π = (List.replicate (cUD π + 1) [true, false]).flatten := by
            conv_lhs => rw [dyck_leading π hd hne, hrf]
            rw [List.replicate_succ']; simp
          conv_lhs => rw [hπfud, numNBeforeDD_fUD]
        rw [hrhs]
        have hnd : noDescent (List.replicate (cUD π) false) = true := by
          simpa using noDescent_sorted (cUD π) 0
        rw [tauOf, desComp_noDescent hnd]
        simp only [deltaOf, deltaAux, zero_add, List.zipWith_cons_cons, List.zipWith_nil_left,
          List.headD_cons, add_zero, List.length_replicate]
    · exact psi_valid_head_some n IH π hlen hd hne i hfd
end Psi
