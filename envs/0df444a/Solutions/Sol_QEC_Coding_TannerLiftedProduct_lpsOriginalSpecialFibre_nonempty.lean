-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibre_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:17:15.970266+00:00
-- url     : https://prove2.me/submissions/33516293-34b3-424c-a5cc-0406412e8a24

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFlat
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreToPrimeField_surjective

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0 < N) :
    Nonempty (lpsOriginalSpecialFibre p N hN) := by
  let := lpsOriginalSpecialFibreToPrimeField_surjective p N hN
  let y : Spec (.of (ZMod p)) := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨x, _⟩ := Scheme.Hom.surjective (lpsOriginalSpecialFibreToPrimeField p N hN) y
  exact ⟨x⟩
end QEC.Coding.TannerLiftedProduct
