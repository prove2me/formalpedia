-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_height_add_ringKrullDim_quotient_d92c37b125a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:34:38.382102+00:00
-- url     : https://prove2.me/submissions/40cf26ab-e7a6-44c0-ae08-0fb36896d5be

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_BaseChangeMinimal
import Theorems.Thm_ReciprocityTheory_CA_height_add_ringKrullDim_quotient_mvPolynomial_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open GroundTheory.Heights₂.Heights.Targets.BaseChangeMin
variable {σ : Type*} [Fintype σ] {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
namespace GroundTheory.Heights₂.Heights.Targets.BaseChangeMin
theorem _root_.solution (k : Type*) [Field k]
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ P) = Fintype.card σ := by
  let e : MvPolynomial σ k ≃+* MvPolynomial (Fin (Fintype.card σ)) k :=
    (MvPolynomial.renameEquiv k (Fintype.equivFin σ)).toRingEquiv
  have : (P.map e).IsPrime := Ideal.map_isPrime_of_equiv e
  have h := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field k _ (P.map e)
  rw [RingEquiv.height_map,
    ← ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv P (P.map e) e rfl)] at h
  exact h
end GroundTheory.Heights₂.Heights.Targets.BaseChangeMin
