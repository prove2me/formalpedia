-- Prove2me | solution 1 for PVM.simpleIntegral_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:01.695881+00:00
-- url     : https://prove2.me/submissions/e7cf1371-2e37-45ad-9a38-7f5600899b20

import Definitions.Def_Spectral_PVM_Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.UniformSpace.Dini
import Definitions.Def_Spectral_PVM_Integral

set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E) (z : ℂ) :
    E_pvm.simpleIntegral (SimpleFunc.const ℝ z) = z • 1 := by
  rw [PVM.simpleIntegral, SimpleFunc.range_const, Finset.sum_singleton]
  have hpre : ((SimpleFunc.const ℝ z : SimpleFunc ℝ ℂ) ⁻¹' {z}) = Set.univ := by
    ext t
    simp only [SimpleFunc.const_apply, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_univ]
  rw [hpre, E_pvm.univ]
end PVM
