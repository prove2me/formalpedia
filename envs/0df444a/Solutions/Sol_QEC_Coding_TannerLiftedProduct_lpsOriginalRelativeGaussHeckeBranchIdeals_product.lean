-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeBranchIdeals_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:42:03.640505+00:00
-- url     : https://prove2.me/submissions/7fd14b58-8cec-4995-a17a-6f49edd6db06

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSurjectiveProductKernels_product

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q) *
      (LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q) =
      q.map (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p)) := by
  change RingHom.ker ((RingHom.fst _ _).comp
      (lpsOriginalRelativeGaussHeckeBranchMap N hN p hpN q)) *
    RingHom.ker ((RingHom.snd _ _).comp
      (lpsOriginalRelativeGaussHeckeBranchMap N hN p hpN q)) = _
  rw [lpsOriginalSurjectiveProductKernels_product _
    (lpsOriginalRelativeGaussHeckeBranchMap_surjective N hN p hpN q)]
  ext x
  change lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q
    (Ideal.Quotient.mk _ x) = 0 ↔ _
  rw [← map_zero (lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q),
    (lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q).injective.eq_iff,
    Ideal.Quotient.eq_zero_iff_mem]
  rfl
end QEC.Coding.TannerLiftedProduct
