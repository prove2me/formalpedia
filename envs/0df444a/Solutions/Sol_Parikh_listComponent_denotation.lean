-- Prove2me | solution 1 for Parikh.listComponent_denotation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:52:34.378796+00:00
-- url     : https://prove2.me/submissions/4ff55325-57fc-42e6-8fb2-5660038a0abe

module
public import Definitions.Def_LeanPool_Parikh_ActivationAlgorithm
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
public import Definitions.Def_LeanPool_Parikh_CompilerSupport
public import Theorems.Thm_Parikh_Component_denotation_eq_vadd_closure


set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution {T N : Type*} [DecidableEq T]
    [DecidableEq (ParseTree T N)]
    (B : ParseTree T N) (D : List (ParseTree T N)) (hD : D.Nodup) :
    (listComponent B D).denotation = (contextComponent B D.toFinset).denotation := by
  classical
  have hbase : (listComponent B D).base = (contextComponent B D.toFinset).base := by
    change B.weight + (D.map ParseTree.weight).sum = B.weight + ∑ C ∈ D.toFinset, C.weight
    rw [List.sum_toFinset ParseTree.weight hD]
  have hrange : Set.range (listComponent B D).periods.get =
      Set.range (contextComponent B D.toFinset).periods.get := by
    ext w
    simp [listComponent, contextComponent]
  rw [Component.denotation_eq_vadd_closure, Component.denotation_eq_vadd_closure,
    hbase, hrange]
end Parikh
