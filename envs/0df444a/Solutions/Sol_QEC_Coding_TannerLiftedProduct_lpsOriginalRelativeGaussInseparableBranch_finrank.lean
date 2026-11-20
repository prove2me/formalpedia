-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussInseparableBranch_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:30:32.887831+00:00
-- url     : https://prove2.me/submissions/fe0d7066-6089-4c60-969c-bd80f5e8ec6c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Module.finrank (LPSOriginalGaussAffineOrder N hN p ⧸ q)
      (LPSOriginalRelativeGaussInseparableBranch N hN p q) = p := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let P : Polynomial K := Polynomial.X^p -
    Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)
  have hn : P ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (Fact.out : p.Prime).pos _
  have hd : Module.finrank K (AdjoinRoot P) = P.natDegree :=
    (AdjoinRoot.powerBasis hn).finrank.trans (AdjoinRoot.powerBasis_dim hn)
  change Module.finrank K (AdjoinRoot P) = p
  rw [hd,Polynomial.natDegree_X_pow_sub_C]
end QEC.Coding.TannerLiftedProduct
