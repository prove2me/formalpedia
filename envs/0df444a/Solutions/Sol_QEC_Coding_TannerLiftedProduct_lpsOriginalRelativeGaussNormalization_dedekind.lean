-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_dedekind
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:32:27.750807+00:00
-- url     : https://prove2.me/submissions/b179380d-0976-4231-be64-20fe6b1ef992

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    IsDedekindDomain (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := by
  let := lpsOriginalRelativeGaussHeckeOrder_dedekind N p hNp h4N hN hpN
  let e := lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN
  let : IsDomain (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := MulEquiv.isDomain (LPSOriginalRelativeGaussHeckeOrder N hN p) e.symm.toMulEquiv
  let : IsNoetherianRing (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := isNoetherianRing_of_ringEquiv (LPSOriginalRelativeGaussHeckeOrder N hN p) e
  let : Ring.DimensionLEOne (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.DimensionLEOne.of_ringEquiv e.symm
  let : IsIntegrallyClosed (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := IsIntegrallyClosed.of_equiv e
  exact {}
end QEC.Coding.TannerLiftedProduct
