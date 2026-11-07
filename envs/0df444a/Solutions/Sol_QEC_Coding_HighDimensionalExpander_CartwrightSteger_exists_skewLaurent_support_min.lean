-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_skewLaurent_support_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:30:04.842872+00:00
-- url     : https://prove2.me/submissions/b34d4c00-8c4c-4f46-9cec-b6747c7c18e1

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentIntSupport_nonempty
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentMonomialUnit_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentMonomialUnit_val


attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_skewLaurentIntSupport

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Multiplicative SkewMonoidAlgebra
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    {f : CartwrightStegerSkewLaurentRing P r} (hf : f ≠ 0) :
    ∃ a : ℤ, Multiplicative.ofAdd a ∈ f.support ∧
      ∀ x, Multiplicative.ofAdd x ∈ f.support → a ≤ x := by
  let s := skewLaurentIntSupport P r f
  have hs : s.Nonempty := skewLaurentIntSupport_nonempty P r hf
  let a := s.min' hs
  refine ⟨a, ?_, ?_⟩
  · exact (mem_skewLaurentIntSupport P r f a).mp (s.min'_mem hs)
  · intro x hx
    exact s.min'_le x ((mem_skewLaurentIntSupport P r f x).mpr hx)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
