-- Prove2me | solution 1 for QECCertificates.spanL_map_addSmul_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:38.583284+00:00
-- url     : https://prove2.me/submissions/be9251be-0d80-4ceb-bf90-6e934cc94745

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_subset_spanL
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_addSmul_mem_span
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.addSmul_apply

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (A : List (Vec n)) (w : Vec n) (f : Vec n → ZMod 2) :
    spanL (A.map (fun r => r + f r • w) ++ [w]) = spanL (A ++ [w]) := by
  have hwL : w ∈ spanL (A.map (fun r => r + f r • w) ++ [w]) := subset_spanL (by simp)
  have hwR : w ∈ spanL (A ++ [w]) := subset_spanL (by simp)
  refine le_antisymm ?_ ?_
  · rw [spanL, Submodule.span_le]
    intro x hx
    have hx' : x ∈ A.map (fun r => r + f r • w) ++ [w] := hx
    rw [List.mem_append, List.mem_map] at hx'
    rcases hx' with ⟨r, hr, rfl⟩ | hx'
    · exact addSmul_mem_span _ (subset_spanL (by simp [hr])) hwR
    · exact subset_spanL (by simp [hx'])
  · rw [spanL, Submodule.span_le]
    intro x hx
    have hx' : x ∈ A ++ [w] := hx
    rw [List.mem_append] at hx'
    rcases hx' with hxA | hx'
    · have h1 : x + f x • w ∈ spanL (A.map (fun r => r + f r • w) ++ [w]) :=
        subset_spanL (by simp [List.mem_map_of_mem hxA])
      have h2 : f x • w ∈ spanL (A.map (fun r => r + f r • w) ++ [w]) :=
        Submodule.smul_mem _ _ hwL
      have hmem := Submodule.add_mem _ h1 h2
      simpa [addSmul, add_assoc] using hmem
    · have hxw : x = w := by simpa using hx'
      rw [hxw]; exact hwL
end QECCertificates
