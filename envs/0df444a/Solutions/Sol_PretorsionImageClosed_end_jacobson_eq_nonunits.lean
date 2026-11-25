-- Prove2me | solution 1 for PretorsionImageClosed.end_jacobson_eq_nonunits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:15:53.290514+00:00
-- url     : https://prove2.me/submissions/8878078b-942b-4a77-a4b2-48e3fb738e32

module
public import Mathlib.RingTheory.Artinian.Ring
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
public import Theorems.Thm_PretorsionImageClosed_endNonunitsIdeal_isMaximal
public import Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_nontrivial


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Function
open PretorsionImageClosed
universe u v
variable {A : Type u} {X : Type v}
variable [Ring A] [AddCommGroup X] [Module A X]
namespace PretorsionImageClosed
theorem _root_.solution
    (hX : PretorsionImageClosed.IsIndecomposableModule A X)
    (hXlen : IsFiniteLength A X) :
    Ring.jacobson (Module.End A X) =
      endNonunitsIdeal hX hXlen := by
  letI : Nontrivial X := hX.nontrivial
  apply le_antisymm
  · letI : (endNonunitsIdeal hX hXlen).IsMaximal :=
      endNonunitsIdeal_isMaximal hX hXlen
    exact Ring.jacobson_le_of_isMaximal
      (endNonunitsIdeal hX hXlen)
  · rw [Ring.jacobson_eq_sInf_isMaximal]
    apply le_sInf
    intro J hJ
    have hJmax : J.IsMaximal := hJ
    have hJI : J ≤ endNonunitsIdeal hX hXlen := by
      intro f hf
      exact coe_subset_nonunits hJmax.ne_top hf
    have hEq : J = endNonunitsIdeal hX hXlen :=
      hJmax.eq_of_le
        (Ideal.IsMaximal.ne_top
          (endNonunitsIdeal_isMaximal hX hXlen))
        hJI
    exact hEq.ge
end PretorsionImageClosed
