-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.isZero_interval_obj_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:40:12.998064+00:00
-- url     : https://prove2.me/submissions/36b4a93b-8b4e-40fa-b5c1-32e5c222d015

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_interval_obj
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_isZero_iff_subsingleton


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable (k : Type u) [Field k]
variable {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {a d i : Fin n} (h : ¬ (a ≤ i ∧ i ≤ d)) :
    IsZero ((interval k a d).obj i) := by
  rw [FGModuleCat.isZero_iff_subsingleton, interval_obj]
  change Subsingleton (intervalSpace k a d i)
  rw [Submodule.subsingleton_iff_eq_bot]
  exact intervalSpace_of_not_mem k h
end PretorsionImageClosed.LinearQuiver
