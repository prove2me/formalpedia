-- Prove2me | solution 1 for PVM.simpleIntegral_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:57:27.686815+00:00
-- url     : https://prove2.me/submissions/3aa70fac-2725-4c9c-93e1-a0eddf6465fb

import Definitions.Def_Spectral_PVM_Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.UniformSpace.Dini
import Definitions.Def_Spectral_PVM_Integral
import Theorems.Thm_PVM_simpleIntegral_add
import Theorems.Thm_PVM_simpleIntegral_neg

set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E) (f g : SimpleFunc ℝ ℂ) :
    E_pvm.simpleIntegral (f - g) = E_pvm.simpleIntegral f - E_pvm.simpleIntegral g := by
  rw [sub_eq_add_neg, E_pvm.simpleIntegral_add, E_pvm.simpleIntegral_neg]
  rw [sub_eq_add_neg]
end PVM
