-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalZero_verticalDenominatorsDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:36:41.66376+00:00
-- url     : https://prove2.me/submissions/0a73067c-7917-42f4-9080-350957283b5a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Unramified.Locus
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalVerticalUnramified
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalZero_heightOne_verticalUnder


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime lpsOriginalGaussPrime_principal
attribute [local instance] gaussFiberBaseFieldAlgebra gaussFiberNormalizationCommRing
  gaussFiberNormalizationRing gaussFiberNormalizationSemiring verticalPrimeJAlgebra
  verticalPrimeBaseFieldAlgebra verticalPrimeNormalCommRing verticalPrimeNormalRing
  verticalPrimeNormalSemiring
variable (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
local notation "K" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "C" => integralClosure (Polynomial ℤ) K
local notation "D" => integralClosure (LPSOriginalGaussBase p) K
include hN
omit [NeZero N]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (q : Ideal C) [q.IsPrime] (hq : q.height = 1) (hpq : (p : C) ∈ q) :
    Disjoint (Algebra.algebraMapSubmonoid C (lpsOriginalGaussPrime p).primeCompl : Set C)
      (q : Set C) := by
  apply Set.disjoint_left.mpr
  intro x hx hxq
  obtain ⟨f,hf,rfl⟩ := hx
  have hfq : f ∈ q.under (Polynomial ℤ) := hxq
  rw [lpsOriginalNormalZero_heightOne_verticalUnder N hN p q hq hpq] at hfq
  exact hf hfq
end QEC.Coding.TannerLiftedProduct
