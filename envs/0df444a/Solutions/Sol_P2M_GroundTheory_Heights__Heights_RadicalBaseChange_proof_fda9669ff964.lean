-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RadicalBaseChange_proof_fda9669ff964
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:01:35.436912+00:00
-- url     : https://prove2.me/submissions/089d4a70-4b7d-4722-b2fc-71363b36b7a9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ReducedTensorPerfect
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRadicalBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_of_perfectField_028675d24e8d


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
namespace GroundTheory.Heights₂.Heights
namespace RadicalBaseChange
theorem _root_.solution : RadicalBaseChange.Statement := by
  intro K L _ _ _ σ ι I hI
  let : Algebra K L := σ.toAlgebra
  rw [Ideal.isRadical_iff_quotient_reduced] at hI ⊢
  have h1 : IsReduced (L ⊗[K] (MvPolynomial ι K ⧸ I)) :=
    isReduced_tensorProduct_of_perfectField K L _
  let e1 := Algebra.TensorProduct.tensorQuotientEquiv (R := K) L (MvPolynomial ι K) L I
  let e2 : L ⊗[K] MvPolynomial ι K ≃ₐ[L] MvPolynomial ι L := MvPolynomial.algebraTensorAlgEquiv K L
  have hmap : I.map (MvPolynomial.map σ) =
      (I.map (Algebra.TensorProduct.includeRight (R := K) (A := L))).map
        (e2 : L ⊗[K] MvPolynomial ι K →+* MvPolynomial ι L) := by
    rw [← Ideal.map_coe (Algebra.TensorProduct.includeRight (R := K) (A := L)), Ideal.map_map]
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [e2, MvPolynomial.algebraTensorAlgEquiv_tmul, RingHom.algebraMap_toAlgebra]
    · intro i
      simp [e2, MvPolynomial.algebraTensorAlgEquiv_tmul]
  let e3 := Ideal.quotientEquivAlg (I.map (Algebra.TensorProduct.includeRight (R := K) (A := L)))
    (I.map (MvPolynomial.map σ)) e2 hmap
  exact isReduced_of_injective (e1.toRingEquiv.trans e3.toRingEquiv).symm (RingEquiv.injective _)
end RadicalBaseChange
end GroundTheory.Heights₂.Heights
