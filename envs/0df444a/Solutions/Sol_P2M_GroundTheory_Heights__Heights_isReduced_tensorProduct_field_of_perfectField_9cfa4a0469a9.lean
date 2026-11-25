-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_field_of_perfectField_9cfa4a0469a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:42:36.369379+00:00
-- url     : https://prove2.me/submissions/18acb3fc-f54e-4d83-bd0a-8cb9888e5f0d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ReducedTensorPerfect
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_of_isSeparable_2807efad16d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isReduced_fractionRing_mvPolynomial_tensorProduct_8beeb3405729

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
set_option synthInstance.maxHeartbeats 400000
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (K : Type u) [Field K] [PerfectField K]
    (L : Type u) [Field L] [Algebra K L] (E : Type u) [Field E] [Algebra K E]
    [Algebra.EssFiniteType K E] : IsReduced (L ⊗[K] E) := by
  obtain ⟨s, hs, H⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K E
  let F := IntermediateField.adjoin K (s : Set E)
  have : Algebra.EssFiniteType F E := Algebra.EssFiniteType.of_comp K F E
  let e : FractionRing (MvPolynomial s K) ≃ₐ[K] F :=
    hs.1.aevalEquivField.trans (IntermediateField.equivOfEq (by simp [F]))
  have : IsReduced (FractionRing (MvPolynomial s K) ⊗[K] L) :=
    isReduced_fractionRing_mvPolynomial_tensorProduct K s L
  have : IsReduced (F ⊗[K] L) :=
    isReduced_of_injective (Algebra.TensorProduct.congr e.symm AlgEquiv.refl).toAlgHom
      (AlgEquiv.injective _)
  have hD := isReduced_tensorProduct_of_isSeparable (F := F) (E := E) (F ⊗[K] L)
  exact @isReduced_of_injective _ _ _ _ _ _ _
    ((Algebra.TensorProduct.comm K L E).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange K F F E L).symm.toRingEquiv)
    (RingEquiv.injective _) hD
end GroundTheory.Heights₂.Heights
