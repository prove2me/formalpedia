-- Prove2me | solution 1 for Potential.rectangle_vertices_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:04:34.196801+00:00
-- url     : https://prove2.me/submissions/3ce28a75-9845-47eb-bbf7-51ab6c69e295

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Max
public import Definitions.Def_MondererShapley_Solution
public import Theorems.Thm_Potential_rectangle_return
public import Theorems.Thm_Potential_vertices_nil
public import Theorems.Thm_Potential_vertices_cons

set_option autoImplicit true
@[expose] public section
public section
open Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]
namespace Potential
theorem _root_.solution (s : Profile A) (i j : I) (hij : i ≠ j)
    (a : A i) (b : A j) (ha : a ≠ s i) (hb : b ≠ s j) :
    (vertices s [⟨i, a⟩, ⟨j, b⟩, ⟨i, s i⟩, ⟨j, s j⟩]).dropLast.Nodup := by
  have hsB : s ≠ Function.update s i a := by
    intro he
    exact ha (by simpa using (congrFun he i).symm)
  have hsC : s ≠ Function.update (Function.update s i a) j b := by
    intro he
    exact ha (by simpa [hij] using (congrFun he i).symm)
  have hsD : s ≠ Function.update s j b := by
    intro he
    exact hb (by simpa using (congrFun he j).symm)
  have hBC : Function.update s i a ≠ Function.update (Function.update s i a) j b := by
    intro he
    exact hb (by simpa [Ne.symm hij] using (congrFun he j).symm)
  have hBD : Function.update s i a ≠ Function.update s j b := by
    intro he
    exact ha (by simpa [hij] using congrFun he i)
  have hCD : Function.update (Function.update s i a) j b ≠ Function.update s j b := by
    intro he
    exact ha (by simpa [hij] using congrFun he i)
  simp only [vertices_cons, vertices_nil, List.dropLast_cons_cons, List.dropLast_singleton]
  rw [rectangle_return s i j hij a b]
  simp [List.nodup_cons, hsB, hsC, hsD, hBC, hBD, hCD]
end Potential
