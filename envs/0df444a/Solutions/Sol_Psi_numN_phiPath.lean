-- Prove2me | solution 1 for Psi.numN_phiPath
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:30:55.452634+00:00
-- url     : https://prove2.me/submissions/16e9255e-ecd6-482c-a776-6b57baf7ba0a

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic
import Theorems.Thm_Psi_len_filter_split
import Theorems.Thm_Psi_numN_append
import Theorems.Thm_Psi_numN_replicate_true
import Theorems.Thm_Psi_numN_replicate_false
import Theorems.Thm_Psi_numN_fUD
import Theorems.Thm_Psi_numN_single_true
import Theorems.Thm_Psi_numN_flatten_pair
import Theorems.Thm_Psi_noDescent_false_decomp
import Theorems.Thm_Psi_splitAtRow_append


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w : List Bool) (av : List ℕ) : numN (phiPath w av) = w.length + 1 := by
  fun_induction phiPath w av with
  | case1 w av hnd =>
      simp only [numN_append, numN_flatten_pair, numN_replicate_true, numN_replicate_false,
        add_zero]
      have := len_filter_split w
      omega
  | case2 w av hnd a after0 b w' hh av' pi rho rho' hsplit ihrec =>
      have hdec : w = List.replicate a false ++ List.replicate b true ++ false :: w' :=
        (noDescent_false_decomp (by simpa using hnd)).1
      have happ : rho ++ rho' = pi := by
        have := splitAtRow_append pi hh; rw [hsplit] at this; simpa using this
      have hsum : numN rho + numN rho' = w'.length + 1 := by
        rw [← numN_append, happ, ihrec]
      have hwlen : w.length = a + b + 1 + w'.length := by
        rw [hdec]; simp [List.length_append]; omega
      rw [show (List.replicate a [true, false]).flatten = fUD a from rfl,
          numN_append, numN_append, numN_append, numN_append, numN_append, numN_fUD,
          numN_single_true, numN_replicate_true, numN_replicate_false]
      omega
end Psi
