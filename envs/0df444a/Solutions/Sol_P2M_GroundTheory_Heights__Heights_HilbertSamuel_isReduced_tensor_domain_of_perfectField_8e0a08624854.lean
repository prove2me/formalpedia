-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_isReduced_tensor_domain_of_perfectField_8e0a08624854
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:42:11.038854+00:00
-- url     : https://prove2.me/submissions/3e09fdfb-d850-4fa5-a2e3-c76be77e835c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPrimeComplexRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PPrimeComplexRadical
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_isReduced_tensor_field_of_perfectField_ecf314672c96

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial TensorProduct
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (K A F : Type*) [Field K] [PerfectField K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [Field F] [Algebra K F] :
    IsReduced (F ⊗[K] A) := by
  have : Algebra.EssFiniteType A (FractionRing A) :=
    .of_isLocalization _ (nonZeroDivisors A)
  have : Algebra.EssFiniteType K (FractionRing A) := .comp K A _
  have := isReduced_tensor_field_of_perfectField K (FractionRing A) F
  have : IsReduced (F ⊗[K] FractionRing A) :=
    isReduced_of_injective (Algebra.TensorProduct.comm K F (FractionRing A)) (AlgEquiv.injective _)
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id K F) (IsScalarTower.toAlgHom K A (FractionRing A)))
    (Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective A _))
end GroundTheory.Heights₂.Heights.HilbertSamuel
