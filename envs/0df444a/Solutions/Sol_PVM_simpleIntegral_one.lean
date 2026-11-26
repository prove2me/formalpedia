-- Prove2me | solution 1 for PVM.simpleIntegral_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:23.370961+00:00
-- url     : https://prove2.me/submissions/a899cc6f-cd44-4728-8552-2ec06013bd25

import Definitions.Def_Spectral_PVM_Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.UniformSpace.Dini
import Definitions.Def_Spectral_PVM_Integral
import Theorems.Thm_PVM_simpleIntegral_const
import Theorems.Thm_PVM_simpleIntegral_zero
attribute [local simp] PVM.simpleIntegral_zero

set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E) :
    E_pvm.simpleIntegral (1 : SimpleFunc ℝ ℂ) = 1 := by
  rw [show (1 : SimpleFunc ℝ ℂ) = SimpleFunc.const ℝ 1 by
    ext t
    rfl]
  rw [E_pvm.simpleIntegral_const, one_smul]
end PVM
