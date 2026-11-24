-- Prove2me | solution 1 for Psi.isValid_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:38:09.181718+00:00
-- url     : https://prove2.me/submissions/0b84dfa6-9bdc-4dc4-9aaf-b76c79607db4

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_desComp_descent
import Theorems.Thm_Psi_deltaOf_length
import Theorems.Thm_Psi_isChain_map_add_reflect
import Theorems.Thm_Psi_desComp_ne_nil
import Theorems.Thm_Psi_w_length_descent
import Theorems.Thm_Psi_tauOf_descent

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w : List Bool) (av : List ℕ) (hv : IsValid w av)
    (hnd : noDescent w = false) :
    IsValid ((w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1)) av.tail := by
  obtain ⟨hlen, hchain, hlast⟩ := hv
  cases av with
  | nil => rw [desComp_descent hnd] at hlen; simp at hlen
  | cons ha av' =>
    have hwl := w_length_descent hnd
    rw [desComp_descent hnd] at hlen
    simp only [List.length_cons] at hlen
    rw [tauOf_descent hnd] at hchain hlast
    simp only [List.tail_cons]
    set c := cLead0 w + 1 + cLead1 (w.drop (cLead0 w)) with hcdef
    set w' := (w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1) with hw'def
    have hlen' : av'.length = (desComp (false :: w')).length := by omega
    have hne : tauOf w' av' ≠ [] := by
      have hpos : 0 < (tauOf w' av').length := by
        rw [tauOf, List.length_zipWith, deltaOf_length, hlen', min_self]
        exact List.length_pos_of_ne_nil (desComp_ne_nil _)
      exact List.ne_nil_of_length_pos hpos
    refine ⟨hlen', ?_, ?_⟩
    · exact isChain_map_add_reflect _ c (List.IsChain.of_cons hchain)
    · have hM : (tauOf w' av').map (· + c) ≠ [] := by simpa using hne
      have hcl : ((c + ha) :: (tauOf w' av').map (· + c)).getLast?
          = ((tauOf w' av').map (· + c)).getLast? := by
        obtain ⟨z, zs, hz⟩ := List.exists_cons_of_ne_nil hM
        rw [hz]; simp [List.getLast?_cons_cons]
      rw [hcl, List.getLast?_map] at hlast
      obtain ⟨g, hg, hgc⟩ := Option.map_eq_some_iff.mp hlast
      rw [hg]; congr 1; omega
end Psi
