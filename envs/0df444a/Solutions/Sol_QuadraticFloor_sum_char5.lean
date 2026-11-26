-- Prove2me | solution 1 for QuadraticFloor.sum_char5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:01:10.373153+00:00
-- url     : https://prove2.me/submissions/5251f4c4-c841-49e7-9fa6-e59bdb95f359

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
public import Theorems.Thm_QuadraticFloor_xi_two
public import Theorems.Thm_QuadraticFloor_one_two
public import Theorems.Thm_QuadraticFloor_xixi_two
public import Theorems.Thm_QuadraticFloor_starxi_two
public import Theorems.Thm_QuadraticFloor_univ_char5

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
namespace QuadraticFloor
theorem _root_.solution {M : Type*} [AddCommMonoid M] (F : DirichletCharacter ℂ 5 → M) :
    ∑ ψ, F ψ = F 1 + F xi + F (xi * xi) + F (star xi) := by
  have hv : ∀ ψ ψ' : DirichletCharacter ℂ 5, ψ 2 ≠ ψ' 2 → ψ ≠ ψ' := fun ψ ψ' h e => h (e ▸ rfl)
  have n1 : (1 : DirichletCharacter ℂ 5) ∉ ({xi, xi * xi, star xi} : Finset _) := by
    simp only [mem_insert, mem_singleton, not_or]
    refine ⟨hv _ _ ?_, hv _ _ ?_, hv _ _ ?_⟩ <;>
      rw [one_two] <;> simp only [xi_two, xixi_two, starxi_two] <;>
      intro h <;> simp [Complex.ext_iff] at h <;> norm_num at h
  have n2 : xi ∉ ({xi * xi, star xi} : Finset (DirichletCharacter ℂ 5)) := by
    simp only [mem_insert, mem_singleton, not_or]
    refine ⟨hv _ _ ?_, hv _ _ ?_⟩ <;>
      rw [xi_two] <;> simp only [xixi_two, starxi_two] <;>
      intro h <;> simp [Complex.ext_iff] at h <;> norm_num at h
  have n3 : xi * xi ∉ ({star xi} : Finset (DirichletCharacter ℂ 5)) := by
    simp only [mem_singleton]
    refine hv _ _ ?_
    rw [xixi_two, starxi_two]
    intro h; simp [Complex.ext_iff] at h
  rw [univ_char5, sum_insert n1, sum_insert n2, sum_insert n3, sum_singleton, add_assoc, add_assoc]
end QuadraticFloor
