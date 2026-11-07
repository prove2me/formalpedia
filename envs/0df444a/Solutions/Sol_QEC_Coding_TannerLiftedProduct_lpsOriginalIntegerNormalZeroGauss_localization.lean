-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroGauss_localization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:32:30.268103+00:00
-- url     : https://prove2.me/submissions/befb8045-5994-4660-9d0e-dc1bebfc3e1a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.Height
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerBaseFractionMap_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime lpsOriginalGaussPrime_principal
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
    let := (lpsOriginalIntegerNormalZeroToGaussNormalization N hN p).toAlgebra
    IsLocalization
      (Algebra.algebraMapSubmonoid
        (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN))
        (lpsOriginalGaussPrime p).primeCompl)
      (integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
  let := lpsOriginalGaussBase_scalarTower N hN p
  let C := integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)
  let D := integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN)
  let instCD : Algebra C D :=
    (lpsOriginalIntegerNormalZeroToGaussNormalization N hN p).toAlgebra
  let : SMul C D := instCD.toSMul
  let : IsScalarTower C D (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    ⟨fun c d x => by
      change (c.val*d.val)*x=c.val*(d.val*x)
      exact mul_assoc _ _ _⟩
  let : IsScalarTower (Polynomial ℤ) C D :=
    .of_algebraMap_eq' (by
      apply RingHom.ext
      intro f
      apply Subtype.ext
      rfl)
  let M := (lpsOriginalGaussPrime p).primeCompl
  let : IsLocalization (Algebra.algebraMapSubmonoid (lpsOriginalGeneratedFunctionFieldQ N hN) M)
      (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    IsLocalization.of_le_isUnit (fun x hx => by
      obtain ⟨f,hf,rfl⟩ := hx
      apply isUnit_iff_ne_zero.mpr
      intro hz
      have hinj : Function.Injective (lpsOriginalIntegerBaseToGeneratedField N hN) :=
        (algebraMap (FractionRing (Polynomial ℚ))
          (lpsOriginalGeneratedFunctionFieldQ N hN)).injective.comp
          lpsOriginalIntegerBaseFractionMap_injective
      have hf0 : f = 0 := hinj (hz.trans (lpsOriginalIntegerBaseToGeneratedField N hN).map_zero.symm)
      exact hf (hf0 ▸ Ideal.zero_mem _))
  exact IsLocalization.integralClosure (R := Polynomial ℤ)
    (S := lpsOriginalGeneratedFunctionFieldQ N hN) (Rf := LPSOriginalGaussBase p)
    (Sf := lpsOriginalGeneratedFunctionFieldQ N hN) M
end QEC.Coding.TannerLiftedProduct
