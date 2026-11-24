-- Prove2me | solution 1 for Psi.numNBeforeDD_reconstruct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:47:41.646562+00:00
-- url     : https://prove2.me/submissions/1fbbd51a-56ef-460d-8f00-07d31925963f

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
import Theorems.Thm_Psi_numNBeforeDD_append
import Theorems.Thm_Psi_hasDD_append_false
import Theorems.Thm_Psi_hasDD_fUD
import Theorems.Thm_Psi_hasDD_replicate_true
import Theorems.Thm_Psi_numN_append
import Theorems.Thm_Psi_numN_fUD
import Theorems.Thm_Psi_numN_replicate_true
import Theorems.Thm_Psi_stEast_append


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a b : ℕ) (ρ ρ' : List Bool) (hb : 1 ≤ b)
    (hρDD : hasDD ρ = false) :
    numNBeforeDD ((List.replicate a [true, false]).flatten ++ [true] ++ ρ
        ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ')
      = a + 1 + numN ρ + b := by
  rw [show (List.replicate a [true, false]).flatten = fUD a from rfl]
  set s := fUD a ++ [true] ++ ρ ++ List.replicate b true with hsdef
  have hwhole : fUD a ++ [true] ++ ρ ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ'
      = s ++ (List.replicate (b + 1) false ++ ρ') := by rw [hsdef]; simp [List.append_assoc]
  rw [hwhole]
  have hs1 : hasDD (fUD a ++ [true]) = false :=
    hasDD_append_false (fUD a) [true] (hasDD_fUD a) rfl (fun _ => by simp)
  have hs2 : hasDD (fUD a ++ [true] ++ ρ) = false := by
    apply hasDD_append_false _ ρ hs1 hρDD
    intro h; rw [stEast_append] at h; simp [stEast] at h
  have hs : hasDD s = false := by
    rw [hsdef]
    apply hasDD_append_false _ (List.replicate b true) hs2 (hasDD_replicate_true b)
    intro _
    obtain ⟨b', rfl⟩ : ∃ b', b = b'+1 := ⟨b-1, by omega⟩
    rw [List.replicate_succ]; simp
  have hsgl : s.getLast? = some true := by
    rw [hsdef]
    obtain ⟨b', rfl⟩ : ∃ b', b = b'+1 := ⟨b-1, by omega⟩
    rw [List.getLast?_append]; simp [List.getLast?_replicate]
  have hbnd : ¬ (s.getLast? = some false ∧
      (List.replicate (b+1) false ++ ρ').head? = some false) := by
    rintro ⟨h1, _⟩; rw [hsgl] at h1; simp at h1
  rw [numNBeforeDD_append s _ hs hbnd]
  have h0 : numNBeforeDD (List.replicate (b+1) false ++ ρ') = 0 := by
    obtain ⟨b', rfl⟩ : ∃ b', b = b'+1 := ⟨b-1, by omega⟩
    rw [show b'+1+1 = b'+2 from rfl, List.replicate_succ, List.replicate_succ, List.cons_append,
      List.cons_append]; rfl
  have hns : numN s = a + 1 + numN ρ + b := by
    rw [hsdef, numN_append, numN_append, numN_append, numN_fUD, numN_replicate_true,
      show numN ([true] : List Bool) = 1 from rfl]
  rw [h0, hns]; omega
end Psi
