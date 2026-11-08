-- Prove2me | solution 1 for QEC.Coding.FiberBundle.finrank_middleHomology_eq_r
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:29:56.721656+00:00
-- url     : https://prove2.me/submissions/d6cfc441-65bd-482d-ad57-8ca7fa38f285

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_CohomologyDimension
import Theorems.Thm_QEC_Coding_FiberBundle_finrank_hho20BaseCohomology_eq
import Theorems.Thm_QEC_Coding_FiberBundle_baseCohomologyToBundleCohomology_surjective
import Theorems.Thm_QEC_Coding_FiberBundle_finrank_middleCohomology_eq_middleHomology
import Theorems.Thm_QEC_Coding_FiberBundle_r_le_finrank_middleHomology


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample) :
    Module.finrank (ZMod 2)
      (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleHomology = r := by
  let K := chainComplex
    (RandomTwist.fiberBundleData baseSample twistSample)
  change Module.finrank (ZMod 2) K.middleHomology = r
  have hUpper :
      Module.finrank (ZMod 2) K.middleCohomology ≤ r := by
    calc
      Module.finrank (ZMod 2) K.middleCohomology ≤
          Module.finrank (ZMod 2) (HHO20BaseCohomology baseSample) :=
        LinearMap.finrank_le_finrank_of_surjective
          (baseCohomologyToBundleCohomology_surjective
            baseSample twistSample hRank)
      _ = r := finrank_hho20BaseCohomology_eq baseSample hRank
  have hLower :
      r ≤ Module.finrank (ZMod 2) K.middleHomology :=
    r_le_finrank_middleHomology baseSample twistSample hRank
  rw [finrank_middleCohomology_eq_middleHomology K] at hUpper
  omega
end QEC.Coding.FiberBundle
