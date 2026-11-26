-- Prove2me | solution 1 for PVM.norm_simpleIntegral_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:10.75066+00:00
-- url     : https://prove2.me/submissions/d9ccc436-3040-4455-81c5-7c2913d6920a

import Definitions.Def_Spectral_PVM_Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.UniformSpace.Dini
import Definitions.Def_Spectral_PVM_Integral
import Theorems.Thm_PVM_simpleIntegral_sub
import Theorems.Thm_PVM_norm_simpleIntegral_le

set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E) (f g : SimpleFunc ℝ ℂ) {C : ℝ}
    (hbdd : ∀ t, ‖f t - g t‖ ≤ C) :
    ‖E_pvm.simpleIntegral f - E_pvm.simpleIntegral g‖ ≤ C := by
  rw [← E_pvm.simpleIntegral_sub]
  apply E_pvm.norm_simpleIntegral_le
  intro t
  exact hbdd t
end PVM
