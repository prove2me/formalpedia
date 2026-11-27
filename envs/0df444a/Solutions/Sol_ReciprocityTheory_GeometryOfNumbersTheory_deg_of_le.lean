-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.deg_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:28:49.703564+00:00
-- url     : https://prove2.me/submissions/d83cd063-6547-40be-959a-838e324a03d5

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStB
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ArakelovDegreeEqDegreeOfFamily
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_exists_isFrame
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_arakelovDegree_eq_degreeOfFamily
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_IsFrame_ds_spanK_eq
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_IsFrame_relIndex_span_frame_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (h : HermFam K V) {E' E : Submodule (𝓞 K) V} (hE' : E'.FG) (hE : E.FG)
    (hle : E' ≤ E) (hspan : (E : Set V) ⊆ Submodule.span K (E' : Set V)) :
    deg h E' = deg h E -
      Real.log (E'.toAddSubgroup.relIndex E.toAddSubgroup : ℝ) / finrank ℚ K := by
  obtain ⟨v, hv⟩ := exists_isFrame E' hE'
  have hvE : IsFrame K E v := by
    refine ⟨fun i => hle (hv.1 i), hv.2.1, ?_⟩
    intro x hx
    have hx' := hspan hx
    rw [← hv.ds_spanK_eq] at hx'
    exact hx'
  rw [arakelovDegree_eq_degreeOfFamily h hE' hv, arakelovDegree_eq_degreeOfFamily h hE hvE]
  unfold degreeOfFamily
  have hS : Submodule.span (𝓞 K) (Set.range v) ≤ E' :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hv.1)
  have hmul := AddSubgroup.relIndex_mul_relIndex
    (H := (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup) (K := E'.toAddSubgroup)
    (L := E.toAddSubgroup) (fun x hx => hS hx) (fun x hx => hle hx)
  have ha := hv.relIndex_span_frame_ne_zero hE'
  have hc := hvE.relIndex_span_frame_ne_zero hE
  have hb : E'.toAddSubgroup.relIndex E.toAddSubgroup ≠ 0 := fun h0 =>
    hc (by rw [← hmul, h0, mul_zero])
  have hlog : Real.log
      ((Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup : ℝ) =
      Real.log ((Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E'.toAddSubgroup : ℝ)
        + Real.log (E'.toAddSubgroup.relIndex E.toAddSubgroup : ℝ) := by
    rw [← hmul, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr hb)]
  rw [hlog]
  ring
end ReciprocityTheory.GeometryOfNumbersTheory
