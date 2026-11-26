-- Prove2me | solution 1 for QuadraticFloor.univ_char5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:01.223989+00:00
-- url     : https://prove2.me/submissions/015a71a1-ffea-444f-bd6c-6cdbfa368e3d

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
public import Theorems.Thm_QuadraticFloor_xi_two
public import Theorems.Thm_QuadraticFloor_char5_ext
public import Theorems.Thm_QuadraticFloor_char5_two
public import Theorems.Thm_QuadraticFloor_one_two
public import Theorems.Thm_QuadraticFloor_xixi_two
public import Theorems.Thm_QuadraticFloor_starxi_two

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution :
    (univ : Finset (DirichletCharacter ℂ 5)) = {1, xi, xi * xi, star xi} := by
  ext ψ
  simp only [mem_univ, mem_insert, mem_singleton, true_iff]
  rcases char5_two ψ with h | h | h | h
  · left; exact char5_ext (h.trans one_two.symm)
  · right; left; exact char5_ext (h.trans xi_two.symm)
  · right; right; left; exact char5_ext (h.trans xixi_two.symm)
  · right; right; right; exact char5_ext (h.trans starxi_two.symm)
end QuadraticFloor
