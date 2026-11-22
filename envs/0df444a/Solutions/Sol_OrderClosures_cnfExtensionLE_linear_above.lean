-- Prove2me | solution 1 for OrderClosures.cnfExtensionLE_linear_above
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:57.279633+00:00
-- url     : https://prove2.me/submissions/a3fa9448-ab06-4cdc-9ff2-7782b1e33459

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
public import Mathlib.SetTheory.Ordinal.Principal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Theorems.Thm_OrderClosures_cnfExtensionLT_linear_above

set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution (ζ : Ordinal.{u})
    {η η' : Ordinal.{u}} (hη : cnfExtensionLE ζ η)
    (hη' : cnfExtensionLE ζ η') :
    cnfExtensionLE η η' ∨ cnfExtensionLE η' η := by
  rcases hη with rfl | hη
  · exact Or.inl hη'
  rcases hη' with rfl | hη'
  · exact Or.inr (Or.inr hη)
  rcases lt_trichotomy η η' with hlt | heq | hgt
  · exact Or.inl (Or.inr ((cnfExtensionLT_linear_above ζ hη hη').mpr hlt))
  · exact Or.inl (Or.inl heq)
  · exact Or.inr (Or.inr ((cnfExtensionLT_linear_above ζ hη' hη).mpr hgt))
end OrderClosures
