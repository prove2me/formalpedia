-- Prove2me | solution 1 for PVM.simpleIntegral_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:57:28.770578+00:00
-- url     : https://prove2.me/submissions/5c347fb1-ce19-4c04-bcf6-3edff4613c3f

import Definitions.Def_Spectral_PVM_Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.UniformSpace.Dini
import Definitions.Def_Spectral_PVM_Integral
import Theorems.Thm_PVM_simpleIntegral_map_mul_map

set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E) (f g : SimpleFunc ℝ ℂ) :
    E_pvm.simpleIntegral (f * g) = E_pvm.simpleIntegral f * E_pvm.simpleIntegral g := by
  rw [SimpleFunc.mul_eq_map₂]
  symm
  simpa only [SimpleFunc.map_fst_pair, SimpleFunc.map_snd_pair] using
    E_pvm.simpleIntegral_map_mul_map (f.pair g) Prod.fst Prod.snd
end PVM
