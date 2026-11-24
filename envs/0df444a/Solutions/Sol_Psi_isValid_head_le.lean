-- Prove2me | solution 1 for Psi.isValid_head_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:38:27.973432+00:00
-- url     : https://prove2.me/submissions/bce5225f-1da6-425a-861f-d0ea0b60ffec

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_desComp_descent
import Theorems.Thm_Psi_deltaOf_length
import Theorems.Thm_Psi_desComp_ne_nil
import Theorems.Thm_Psi_tauOf_descent

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w : List Bool) (av : List ℕ) (hv : IsValid w av)
    (hnd : noDescent w = false) :
    av.headD 0 ≤ (tauOf ((w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1)) av.tail).headD 0 := by
  obtain ⟨hlen, hchain, _⟩ := hv
  cases av with
  | nil => rw [desComp_descent hnd] at hlen; simp at hlen
  | cons ha av' =>
    rw [desComp_descent hnd] at hlen
    simp only [List.length_cons] at hlen
    rw [tauOf_descent hnd] at hchain
    simp only [List.headD_cons, List.tail_cons]
    set c := cLead0 w + 1 + cLead1 (w.drop (cLead0 w)) with hcdef
    set w' := (w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1) with hw'def
    have hlen' : av'.length = (desComp (false :: w')).length := by omega
    have hne : tauOf w' av' ≠ [] := by
      have hpos : 0 < (tauOf w' av').length := by
        rw [tauOf, List.length_zipWith, deltaOf_length, hlen', min_self]
        exact List.length_pos_of_ne_nil (desComp_ne_nil _)
      exact List.ne_nil_of_length_pos hpos
    obtain ⟨x, xs, htau⟩ := List.exists_cons_of_ne_nil hne
    rw [htau] at hchain ⊢
    simp only [List.map_cons, List.headD_cons] at hchain ⊢
    rw [List.isChain_cons_cons] at hchain
    omega
end Psi
