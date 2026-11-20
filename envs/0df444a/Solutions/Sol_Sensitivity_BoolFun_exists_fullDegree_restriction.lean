-- Prove2me | solution 1 for Sensitivity.BoolFun.exists_fullDegree_restriction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:58:31.814064+00:00
-- url     : https://prove2.me/submissions/5f84b3a7-bca6-4a7c-82f2-61b387e05a30

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Definitions.Def_Sensitivity_Subcube
import Theorems.Thm_Sensitivity_BoolFun_restrictTo_moebius_subset
import Theorems.Thm_Sensitivity_BoolFun_exists_degree_witness


set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
namespace BoolFun
theorem _root_.solution (f : BoolFun n) (hd : 0 < f.degree) :
    ∃ S : Finset (Fin n),
      S.card = f.degree ∧
      f.moebius S ≠ 0 ∧
      (f.restrictTo S (fun _ => false)).moebius S ≠ 0 := by
  obtain ⟨S, hcard, hne⟩ := f.exists_degree_witness hd
  exact ⟨S, hcard, hne, by rwa [f.restrictTo_moebius_subset S S Finset.Subset.rfl]⟩
end BoolFun
end Sensitivity
