-- Prove2me | solution 1 for PVM.monotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:45.633809+00:00
-- url     : https://prove2.me/submissions/9a56fb98-112b-4100-af15-4c62d4a85d1c

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Definitions.Def_Spectral_PVM_Basic

set_option autoImplicit false
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E) {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (h : S ⊆ T) (x : E) :
    (@inner ℂ E _ (E_pvm.proj S x) x).re ≤ (@inner ℂ E _ (E_pvm.proj T x) x).re :=
  by
    have hST : S ∩ T = S := Set.inter_eq_left.mpr h
    have hTS : T ∩ S = S := Set.inter_eq_right.mpr h
    have hprojST : E_pvm.proj S * E_pvm.proj T = E_pvm.proj S := by
      rw [← E_pvm.inter S T hS hT, hST]
    have hprojTS : E_pvm.proj T * E_pvm.proj S = E_pvm.proj S := by
      rw [← E_pvm.inter T S hT hS, hTS]
    have hdiff_idempotent :
        IsIdempotentElem (E_pvm.proj T - E_pvm.proj S) :=
      (E_pvm.isOrthogonalProjection S hS).2.sub
        (E_pvm.isOrthogonalProjection T hT).2 hprojST hprojTS
    have hdiff_selfAdjoint :
        IsSelfAdjoint (E_pvm.proj T - E_pvm.proj S) :=
      (E_pvm.isOrthogonalProjection T hT).1.sub
        (E_pvm.isOrthogonalProjection S hS).1
    have hnonneg :=
      ((ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint
        hdiff_idempotent).mpr hdiff_selfAdjoint).re_inner_nonneg_left x
    rw [sub_apply, inner_sub_left, map_sub, sub_nonneg] at hnonneg
    exact hnonneg
end PVM
