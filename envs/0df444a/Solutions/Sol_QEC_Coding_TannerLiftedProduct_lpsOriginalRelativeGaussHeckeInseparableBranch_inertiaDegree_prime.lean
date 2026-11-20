-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeInseparableBranch_inertiaDegree_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:37:23.169317+00:00
-- url     : https://prove2.me/submissions/358909e7-353b-4b9a-b76f-e33ac8e3d403

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussInseparableBranch_finrank

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q).inertiaDeg
      (LPSOriginalGaussAffineOrder N hN p) = p := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_maximal N hN p hpN q
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_liesOver N hN p hpN q
  rw [Ideal.inertiaDeg_eq_of_isMaximal q]
  exact (lpsOriginalRelativeGaussHeckeInseparableBranchResidueEquiv N hN p hpN q).toLinearEquiv.finrank_eq.trans
    (lpsOriginalRelativeGaussInseparableBranch_finrank N hN p q)
end QEC.Coding.TannerLiftedProduct
