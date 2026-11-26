-- Prove2me | solution 1 for PVM.simpleIntegral_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:43.764993+00:00
-- url     : https://prove2.me/submissions/378db4ae-d793-4b95-8558-e1b34e5743a9

import Definitions.Def_Spectral_PVM_Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.UniformSpace.Dini
import Definitions.Def_Spectral_PVM_Integral
import Theorems.Thm_PVM_simpleIntegral_const

set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E) :
    E_pvm.simpleIntegral (0 : SimpleFunc ℝ ℂ) = 0 := by
  rw [show (0 : SimpleFunc ℝ ℂ) = SimpleFunc.const ℝ 0 by
    ext t
    rfl]
  rw [E_pvm.simpleIntegral_const, zero_smul]
end PVM
