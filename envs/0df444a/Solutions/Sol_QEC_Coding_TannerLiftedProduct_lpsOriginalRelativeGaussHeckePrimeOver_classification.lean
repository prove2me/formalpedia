-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckePrimeOver_classification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:45:06.297114+00:00
-- url     : https://prove2.me/submissions/0bfc2ebc-8a8f-441e-aeb4-6a00563a4731

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckeLinearBranchIdeal_maximal
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckeBranchIdeals_product

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (P : Ideal (LPSOriginalRelativeGaussHeckeOrder N hN p)) [P.IsPrime] [P.LiesOver q] :
    P = LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q ∨
      P = LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q := by
  have hmap : q.map (algebraMap (LPSOriginalGaussAffineOrder N hN p)
      (LPSOriginalRelativeGaussHeckeOrder N hN p)) ≤ P :=
    (Ideal.map_le_iff_le_comap).mpr (le_of_eq (P.over_def q))
  rw [AdjoinRoot.algebraMap_eq,← lpsOriginalRelativeGaussHeckeBranchIdeals_product N hN p hpN q] at hmap
  rcases (inferInstance : P.IsPrime).mul_le.mp hmap with hi | hj
  · exact Or.inl ((lpsOriginalRelativeGaussHeckeLinearBranchIdeal_maximal N hN p hpN q).eq_of_le
      (inferInstance : P.IsPrime).ne_top hi).symm
  · exact Or.inr ((lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_maximal N hN p hpN q).eq_of_le
      (inferInstance : P.IsPrime).ne_top hj).symm
end QEC.Coding.TannerLiftedProduct
