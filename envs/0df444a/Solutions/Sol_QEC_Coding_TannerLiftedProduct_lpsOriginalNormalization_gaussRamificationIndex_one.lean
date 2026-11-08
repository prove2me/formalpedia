-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalization_gaussRamificationIndex_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:24:04.341859+00:00
-- url     : https://prove2.me/submissions/46194dbc-b0dd-4ad1-86cd-979a61ba5d62

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.Height
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussNormalization_etale

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime lpsOriginalGaussPrime_principal
variable (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
attribute [local instance] QEC.Coding.TannerLiftedProduct.gaussFiberBaseFieldAlgebra
local notation "D" => integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN)
attribute [local instance] QEC.Coding.TannerLiftedProduct.gaussFiberNormalizationCommRing
attribute [local instance] QEC.Coding.TannerLiftedProduct.gaussFiberNormalizationRing
attribute [local instance] QEC.Coding.TannerLiftedProduct.gaussFiberNormalizationSemiring
include hN
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hpN : ¬ p ∣ N) (q : Ideal D) [q.IsPrime] :
    q.ramificationIdx (LPSOriginalGaussBase p) = 1 := by
  let := lpsOriginalGaussNormalization_etale N hN p hpN
  let : Algebra.IsUnramifiedAt (LPSOriginalGaussBase p) q :=
    (Algebra.formallyUnramified_iff_forall (R := LPSOriginalGaussBase p) (A := D)).mp
      inferInstance ⟨q,inferInstance⟩
  exact Ideal.ramificationIdx_eq_one q (LPSOriginalGaussBase p)
end QEC.Coding.TannerLiftedProduct
