-- Prove2me | solution 1 for PVM.proj_fiber_mul_proj_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:21.493255+00:00
-- url     : https://prove2.me/submissions/c0d8660e-39e2-4d07-9caa-59513c5b891a

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
theorem _root_.solution (E_pvm : PVM E) (f : SimpleFunc ℝ ℂ)
    {z w : ℂ} (hzw : z ≠ w) :
    E_pvm.proj (f ⁻¹' {z}) * E_pvm.proj (f ⁻¹' {w}) = 0 := by
  rw [← E_pvm.inter _ _ (f.measurableSet_fiber z) (f.measurableSet_fiber w)]
  have hinter : (f ⁻¹' {z}) ∩ (f ⁻¹' {w}) = ∅ := by
    ext t
    constructor
    · intro ht
      exact hzw ((Set.mem_singleton_iff.mp ht.1).symm.trans (Set.mem_singleton_iff.mp ht.2))
    · intro ht
      exact False.elim ht
  rw [hinter, E_pvm.empty]
end PVM
