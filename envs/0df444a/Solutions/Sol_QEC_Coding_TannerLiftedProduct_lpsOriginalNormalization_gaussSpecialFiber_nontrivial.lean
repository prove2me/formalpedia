-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalization_gaussSpecialFiber_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:24:09.684469+00:00
-- url     : https://prove2.me/submissions/6915449e-5991-4e21-9540-deffda97832d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.Height
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber

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
theorem _root_.solution (hpN : ¬ p ∣ N) :
    Nontrivial (D ⧸ (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p)).map
        (algebraMap (LPSOriginalGaussBase p) D)) := by
  let : Module.Free (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p) :=
    ((lpsOriginalIntegerPolynomial_monic N hN).map _).free_adjoinRoot
  let : Module.Finite (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p) :=
    ((lpsOriginalIntegerPolynomial_monic N hN).map _).finite_adjoinRoot
  let : Module.Free (LPSOriginalGaussBase p) D :=
    Module.Free.of_equiv (lpsOriginalGaussNormalizationEquiv N hN p hpN).toLinearEquiv
  let : Module.Finite (LPSOriginalGaussBase p) D :=
    Module.Finite.equiv (lpsOriginalGaussNormalizationEquiv N hN p hpN).toLinearEquiv
  obtain ⟨q,hq,hqover⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (R := LPSOriginalGaussBase p) (S := D)
    (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p)) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp
        (FaithfulSMul.algebraMap_injective (LPSOriginalGaussBase p) D)]
      exact bot_le)
  apply Ideal.Quotient.nontrivial_iff.mpr
  exact ne_top_of_le_ne_top hq.ne_top
    (Ideal.map_le_of_le_comap (le_of_eq hqover.symm))
end QEC.Coding.TannerLiftedProduct
