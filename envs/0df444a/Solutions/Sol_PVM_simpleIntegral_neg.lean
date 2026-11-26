-- Prove2me | solution 1 for PVM.simpleIntegral_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:39.310425+00:00
-- url     : https://prove2.me/submissions/0fd102e9-fe22-4efe-beed-f1e24f298634

import Definitions.Def_Spectral_PVM_Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.UniformSpace.Dini
import Definitions.Def_Spectral_PVM_Integral
import Theorems.Thm_PVM_simpleIntegral_map

set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E) (f : SimpleFunc ℝ ℂ) :
    E_pvm.simpleIntegral (-f) = -E_pvm.simpleIntegral f := by
  change E_pvm.simpleIntegral (f.map Neg.neg) = -E_pvm.simpleIntegral f
  rw [E_pvm.simpleIntegral_map, PVM.simpleIntegral, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  rw [neg_smul]
end PVM
