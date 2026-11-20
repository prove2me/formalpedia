-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeInseparableBranchResidue_purelyInseparable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:39:22.004743+00:00
-- url     : https://prove2.me/submissions/0c6805a6-b379-4db7-83ab-3f815e9e539b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussInseparableBranch_purelyInseparable

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_maximal N hN p hpN q
    letI := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_liesOver N hN p hpN q
    letI : Field (LPSOriginalRelativeGaussHeckeOrder N hN p ⧸
        LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q) := Ideal.Quotient.field _
    IsPurelyInseparable (LPSOriginalGaussAffineOrder N hN p ⧸ q)
      (LPSOriginalRelativeGaussHeckeOrder N hN p ⧸
        LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q) := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_maximal N hN p hpN q
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_liesOver N hN p hpN q
  let : Field (LPSOriginalRelativeGaussHeckeOrder N hN p ⧸
      LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q) := Ideal.Quotient.field _
  let := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
  let := lpsOriginalRelativeGaussInseparableBranch_purelyInseparable N hN p hpN q
  exact (lpsOriginalRelativeGaussHeckeInseparableBranchResidueEquiv N hN p hpN q).symm.isPurelyInseparable
end QEC.Coding.TannerLiftedProduct
