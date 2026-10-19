-- Prove2me | solution 1 for TwoDegenerateGraphs.empiricalChildMarginal_entropy_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/c609a46b-5142-4ef3-ac11-9783f1110701

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_abs_binaryEntropy_sub_le_binaryEntropy_abs_sub
import Theorems.Thm_TwoDegenerateGraphs_binaryEntropy_mono_on_half
import Theorems.Thm_TwoDegenerateGraphs_BinaryPairKernel_childMarginal_nonneg
import Theorems.Thm_TwoDegenerateGraphs_BinaryPairKernel_childMarginal_le_one
import Theorems.Thm_TwoDegenerateGraphs_empiricalChildMarginal_mem_Icc
import Theorems.Thm_TwoDegenerateGraphs_empiricalChildMarginal_error

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (parentCount oneCount : ℕ)
    (hparents : 4 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    |binaryEntropy (empiricalChildMarginal parentCount oneCount kernel) -
      binaryEntropy kernel.childMarginal| ≤
        binaryEntropy (1 / (parentCount : ℝ)) := by
  have hparents_two : 2 ≤ parentCount := by omega
  have hempirical := empiricalChildMarginal_mem_Icc
    parentCount oneCount hparents_two hones kernel
  have hchild :
      0 ≤ kernel.childMarginal ∧ kernel.childMarginal ≤ 1 :=
    ⟨BinaryPairKernel.childMarginal_nonneg kernel,
      BinaryPairKernel.childMarginal_le_one kernel⟩
  have hcoupling := empiricalChildMarginal_error
    parentCount oneCount hparents_two hones kernel hparameter
  have hmodulus := abs_binaryEntropy_sub_le_binaryEntropy_abs_sub
    (empiricalChildMarginal parentCount oneCount kernel)
    kernel.childMarginal hempirical.1 hempirical.2 hchild.1 hchild.2
  have hparents_real : (4 : ℝ) ≤ (parentCount : ℝ) := by
    exact_mod_cast hparents
  have hparents_pos : (0 : ℝ) < (parentCount : ℝ) := by
    linarith
  have hhalf : 1 / (parentCount : ℝ) ≤ (2 : ℝ)⁻¹ := by
    apply (div_le_iff₀ hparents_pos).mpr
    norm_num
    linarith
  have hmonotone := binaryEntropy_mono_on_half
    |empiricalChildMarginal parentCount oneCount kernel -
      kernel.childMarginal|
    (1 / (parentCount : ℝ))
    (abs_nonneg _) hcoupling hhalf
  exact hmodulus.trans hmonotone
end TwoDegenerateGraphs
