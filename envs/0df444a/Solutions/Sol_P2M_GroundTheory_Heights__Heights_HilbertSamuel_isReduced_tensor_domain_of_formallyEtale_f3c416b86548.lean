-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_isReduced_tensor_domain_of_formallyEtale_f3c416b86548
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:28.85595+00:00
-- url     : https://prove2.me/submissions/eb50c795-1d5a-48b7-877f-0ea9c4dc1810

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPrimeComplexRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PPrimeComplexRadical

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
theorem _root_.solution (E L D : Type*) [Field E] [Field L] [Algebra E L]
    [Algebra.FormallyEtale E L] [Algebra.EssFiniteType E L] [CommRing D] [IsDomain D]
    [Algebra E D] : IsReduced (L ⊗[E] D) := by
  have : IsReduced (FractionRing D ⊗[E] L) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing D) (FractionRing D ⊗[E] L)
  have : IsReduced (L ⊗[E] FractionRing D) :=
    isReduced_of_injective (Algebra.TensorProduct.comm E L (FractionRing D))
      (AlgEquiv.injective _)
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id E L) (IsScalarTower.toAlgHom E D (FractionRing D)))
    (Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective D _))
end GroundTheory.Heights₂.Heights.HilbertSamuel
