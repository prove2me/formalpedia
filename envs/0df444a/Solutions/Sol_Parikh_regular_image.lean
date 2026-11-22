-- Prove2me | solution 1 for Parikh.regular_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:54:27.280825+00:00
-- url     : https://prove2.me/submissions/83352fb3-bf77-46e6-b054-7889b51e7a6f

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_DFAGrammar
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Theorems.Thm_Parikh_dfaGrammar_language
public import Theorems.Thm_Parikh_treeRepresentation_correct


set_option autoImplicit true
@[expose] public section
public section
open scoped Computability Pointwise
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution [Finite T] [DecidableEq T] (R : Language T) (hR : R.IsRegular) :
    IsSemilinearSet (image R) := by
  classical
  let : Fintype T := Fintype.ofFinite T
  obtain ⟨σ, hσ, M, rfl⟩ := hR
  let : Fintype σ := hσ
  rw [← dfaGrammar_language M]
  exact (treeRepresentation_correct (dfaGrammar M)).2
end Parikh
