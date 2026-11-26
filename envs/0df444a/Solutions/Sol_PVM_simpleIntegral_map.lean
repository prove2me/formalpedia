-- Prove2me | solution 1 for PVM.simpleIntegral_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:01.050529+00:00
-- url     : https://prove2.me/submissions/bcfeb57b-fc97-46df-9bf2-70c4af33bda7

import Definitions.Def_Spectral_PVM_Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.UniformSpace.Dini
import Definitions.Def_Spectral_PVM_Integral
import Theorems.Thm_PVM_sum_proj_preimage

set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E) {β : Type*}
    (f : SimpleFunc ℝ β) (g : β → ℂ) :
    E_pvm.simpleIntegral (f.map g) =
      ∑ y ∈ f.range, g y • E_pvm.proj (f ⁻¹' {y}) := by
  classical
  rw [PVM.simpleIntegral, SimpleFunc.range_map]
  refine Finset.sum_image' _ fun y hy => ?_
  rw [SimpleFunc.map_preimage_singleton, ← E_pvm.sum_proj_preimage,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [(Finset.mem_filter.mp hz).2]
end PVM
