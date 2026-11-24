-- Prove2me | solution 1 for Psi.phi_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:30:48.45807+00:00
-- url     : https://prove2.me/submissions/a4990c08-0110-453c-bf24-955ca32ad7fb

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic
import Theorems.Thm_Psi_len_filter_split
import Theorems.Thm_Psi_noDescent_false_decomp
import Theorems.Thm_Psi_splitAtRow_length


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w : List Bool) (av : List ℕ) :
    (phiPath w av).length = 2 * (w.length + 1) := by
  fun_induction phiPath w av with
  | case1 w av h =>
      have hs := len_filter_split w
      simp only [List.length_append, List.length_flatten, List.map_replicate,
        List.length_replicate, List.sum_replicate, smul_eq_mul, List.length_cons,
        List.length_nil]
      omega
  | case2 w av h a after0 b w' hh av' pi rho rho' hsplit ihrec =>
      have hnd : noDescent w = false := by simpa using h
      have hdec : w = List.replicate a false ++ List.replicate b true ++ false :: w' :=
        (noDescent_false_decomp hnd).1
      have hlen := congrArg List.length hdec
      simp only [List.length_append, List.length_replicate, List.length_cons] at hlen
      have hsp : rho.length + rho'.length = pi.length := by
        have hh2 := splitAtRow_length pi hh
        rw [hsplit] at hh2; simpa using hh2
      have hpi : pi.length = 2 * (w'.length + 1) := ihrec
      simp only [List.length_append, List.length_flatten, List.map_replicate,
        List.length_replicate, List.sum_replicate, smul_eq_mul, List.length_cons,
        List.length_nil]
      omega
end Psi
