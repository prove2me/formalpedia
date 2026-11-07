-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_skewLaurent_support_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:29:46.63344+00:00
-- url     : https://prove2.me/submissions/e0351a20-3a10-4635-835a-1f05df92f59e

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
      ∀ x, Multiplicative.ofAdd x ∈ f.support → x ≤ a := by
  let s := skewLaurentIntSupport P r f
  have hs : s.Nonempty := skewLaurentIntSupport_nonempty P r hf
  let a := s.max' hs
  refine ⟨a, ?_, ?_⟩
  · exact (mem_skewLaurentIntSupport P r f a).mp (s.max'_mem hs)
  · intro x hx
    exact s.le_max' x ((mem_skewLaurentIntSupport P r f x).mpr hx)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
