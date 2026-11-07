-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedForgetLevel_dominant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:12:12.166196+00:00
-- url     : https://prove2.me/submissions/88d0f36b-8b4d-4ae1-8c19-c578844f79d8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    IsDominant (lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM) := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  let X := lpsOriginalIntegerNormalGluedScheme N hN
  let Y := lpsOriginalIntegerNormalGluedScheme M hM
  let f := lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM
  rw [isDominant_iff, denseRange_iff_closure_range, ← Set.univ_subset_iff]
  rw [← isGenericPoint_def.mp (genericPoint_spec X)]
  apply closure_mono
  intro z hz
  have hz' : z = genericPoint X := Set.mem_singleton_iff.mp hz
  subst z
  exact ⟨genericPoint Y,
    lpsOriginalIntegerNormalGluedForgetLevel_generic N M hNM h4N hN hM⟩
end QEC.Coding.TannerLiftedProduct
