-- Prove2me | solution 1 for P2M_MatchingLogic_Necessity_denote_rho__394e8edd322f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:33.396371+00:00
-- url     : https://prove2.me/submissions/5cbc7ef7-7ab1-4c57-acb4-7d03d6446a2a

module
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Necessity
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var



set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Necessity
variable {Var : Type} [DecidableEq Var]
namespace MatchingLogic.Necessity
theorem _root_.solution (x : Var) : M.denote (rho' (Var := Var)) (psi x) = ∅ := by
  ext u
  simp only [psi, denote_app, Model.app, denote_var, Set.mem_ofPred_eq,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨a, ha, hu⟩
  have h0 : a 0 = 2 := ha 0
  simp [h0] at hu
end MatchingLogic.Necessity
