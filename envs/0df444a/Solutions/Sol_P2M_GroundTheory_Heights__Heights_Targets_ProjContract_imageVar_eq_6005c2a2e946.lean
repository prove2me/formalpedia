-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjContract_imageVar_eq_6005c2a2e946
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:02:59.489608+00:00
-- url     : https://prove2.me/submissions/83005189-e000-4389-8f05-5d236aa314d0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_BlockInclInjectiveOfEmbedding
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ProjContract
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjContract_blockIncl_blockEquiv_e7de0e0007e0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Targets.ProjContract
variable {F : Type u} [Field F] {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
namespace GroundTheory.Heights₂.Heights.Targets.ProjContract
theorem _root_.solution (hv : AI.I1.IsBlockMap κ v) (V' : Ideal (Geo.MRingOver F ι')) :
    AI.I1.imageVar F v V' = (FieldNumbers.contractPrime (emb hv) V').comap
      (rename (blockEquiv hv) : Geo.MRingOver F ι →ₐ[F] _).toRingHom := by
  ext x
  simp only [AI.I1.imageVar, FieldNumbers.contractPrime, Ideal.mem_comap, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, rename_rename]
  have : (FieldNumbers.blockIncl (emb hv) ι' ∘ blockEquiv hv) = v := funext (blockIncl_blockEquiv hv)
  rw [this]
end GroundTheory.Heights₂.Heights.Targets.ProjContract
