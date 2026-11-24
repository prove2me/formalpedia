-- Prove2me | solution 1 for Psi.isValid_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:51:16.918401+00:00
-- url     : https://prove2.me/submissions/d51b00f0-8faf-46d1-b643-181c06d62c04

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
import Theorems.Thm_Psi_isChain_map_add
import Theorems.Thm_Psi_cLead0_block
import Theorems.Thm_Psi_cLead1_block
import Theorems.Thm_Psi_deltaOf_length
import Theorems.Thm_Psi_desComp_descent
import Theorems.Thm_Psi_desComp_ne_nil
import Theorems.Thm_Psi_drop_a_block
import Theorems.Thm_Psi_drop_block
import Theorems.Thm_Psi_noDescent_block
import Theorems.Thm_Psi_tauOf_descent


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a b : ℕ) (w' : List Bool) (av' : List ℕ) (hb : 1 ≤ b)
    (hv : IsValid w' av') (h : ℕ) (hh : h ≤ (tauOf w' av').headD 0) :
    IsValid (List.replicate a false ++ List.replicate b true ++ [false] ++ w') (h :: av') := by
  obtain ⟨hlen, hchain, hlast⟩ := hv
  set wb := List.replicate a false ++ List.replicate b true ++ [false] ++ w' with hwbdef
  have hwform : wb = List.replicate a false ++ List.replicate b true ++ false :: w' := by
    rw [hwbdef]; simp [List.append_assoc]
  have hnd : noDescent wb = false := by rw [hwform]; exact noDescent_block a b w' hb
  have hcl0 : cLead0 wb = a := by rw [hwform]; exact cLead0_block a b w' hb
  have hdropa : wb.drop (cLead0 wb) = List.replicate b true ++ false :: w' := by
    rw [hcl0, hwform]; exact drop_a_block a b w'
  have hcl1 : cLead1 (wb.drop (cLead0 wb)) = b := by rw [hdropa]; exact cLead1_block b w'
  have hdropb : (wb.drop (cLead0 wb)).drop (cLead1 (wb.drop (cLead0 wb)) + 1) = w' := by
    rw [hcl1, hdropa]; exact drop_block b w'
  set c := cLead0 wb + 1 + cLead1 (wb.drop (cLead0 wb)) with hcdef
  have htau : tauOf wb (h :: av') = (c + h) :: (tauOf w' av').map (· + c) := by
    rw [tauOf_descent hnd, hdropb]
  have htau_ne : tauOf w' av' ≠ [] := by
    have hpos : 0 < (tauOf w' av').length := by
      rw [tauOf, List.length_zipWith, deltaOf_length, hlen, min_self]
      exact List.length_pos_of_ne_nil (desComp_ne_nil _)
    exact List.ne_nil_of_length_pos hpos
  have hwblen : wb.length = a + b + 1 + w'.length := by
    rw [hwbdef]; simp [List.length_append, List.length_replicate, List.append_assoc]; omega
  have hc_eq : c = a + 1 + b := by rw [hcdef, hcl1, hcl0]
  refine ⟨?_, ?_, ?_⟩
  · rw [desComp_descent hnd, hdropb]; simp only [List.length_cons]; omega
  · rw [htau]
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil htau_ne
    rw [hx]; simp only [List.map_cons]
    rw [List.isChain_cons_cons]
    refine ⟨?_, ?_⟩
    · have hxhd : (tauOf w' av').headD 0 = x := by rw [hx]; rfl
      omega
    · have := isChain_map_add (tauOf w' av') c hchain
      rw [hx] at this; simpa using this
  · rw [htau]
    have hM : (tauOf w' av').map (· + c) ≠ [] := by simpa using htau_ne
    obtain ⟨z, zs, hz⟩ := List.exists_cons_of_ne_nil hM
    rw [hz]; rw [List.getLast?_cons_cons, ← hz, List.getLast?_map, hlast]
    simp only [Option.map_some]
    congr 1
    rw [hwblen, hc_eq]; omega
end Psi
