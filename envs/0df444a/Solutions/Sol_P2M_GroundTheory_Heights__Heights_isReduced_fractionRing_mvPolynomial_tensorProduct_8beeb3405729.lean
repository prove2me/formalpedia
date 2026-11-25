-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isReduced_fractionRing_mvPolynomial_tensorProduct_8beeb3405729
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:33:20.821883+00:00
-- url     : https://prove2.me/submissions/f2ec7d2d-e9d3-4c56-b5b9-08f2bc81fb47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ReducedTensorPerfect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open TensorProduct
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (K : Type u) [Field K] (σ : Type u)
    (L : Type u) [Field L] [Algebra K L] :
    IsReduced (FractionRing (MvPolynomial σ K) ⊗[K] L) := by
  let R := MvPolynomial σ K
  have : IsReduced (R ⊗[K] L) :=
    isReduced_of_injective
      ((Algebra.TensorProduct.comm K R L).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv K L).toRingEquiv)
      (RingEquiv.injective _)
  have : IsReduced (FractionRing R ⊗[R] (R ⊗[K] L)) := by
    let : Algebra (R ⊗[K] L) (FractionRing R ⊗[R] (R ⊗[K] L)) := Algebra.TensorProduct.rightAlgebra
    exact isReduced_localizationPreserves
      (Algebra.algebraMapSubmonoid (R ⊗[K] L) (nonZeroDivisors R))
      (FractionRing R ⊗[R] (R ⊗[K] L)) inferInstance
  exact isReduced_of_injective
    (Algebra.TensorProduct.cancelBaseChange K R R (FractionRing R) L).symm.toAlgHom
    (AlgEquiv.injective _)
end GroundTheory.Heights₂.Heights
