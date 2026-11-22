-- Prove2me | solution 1 for Path.pathEquivEquivalence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:12:21.528613+00:00
-- url     : https://prove2.me/submissions/2766768b-eeab-43fb-a1be-18880e68eefd

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Trace
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Nat.Find
import Definitions.Def_EventStructures_Family_Path
import Theorems.Thm_ConfFamily_Indep_symm
import Theorems.Thm_ConfFamily_TraceEquivFrom_symm
import Theorems.Thm_ConfFamily_TraceEquivFrom_trans


set_option autoImplicit true
variable {L : Type*} (F : ConfFamily L)
open ConfFamily
local infix:50 " ⊢ " => enables F
open Path
local infixr:60 " ≈ₚ " => PathEquiv F
namespace Path
theorem _root_.solution (c₁ c₂ : Conf F) :
    Equivalence (PathEquiv (F := F) (c₁ := c₁) (c₂ := c₂)) where
  refl := (pathEquiv_refl F).refl
  symm h := (pathEquiv_symm F).symm _ _ h
  trans h₁ h₂ := _root_.trans h₁ h₂
end Path
