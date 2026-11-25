-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_specialIdeal_map_26c26a49f2d7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:39:03.340688+00:00
-- url     : https://prove2.me/submissions/08e5861c-e46d-4db2-9b6a-d0bed1746bf4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_ren_apply_85b054347a53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_map_renameEquiv_eq_afd80c1b005a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_ren_apply_8f65176f1b12
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
variable {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k))
omit [DecidableEq K₁] [DecidableEq K₂]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
theorem _root_.solution (W : Ideal (MRing ι₁ O)) :
    specialIdeal (W.map (ren (R := O) σ : MRing ι₁ O →+* MRing ι₂ O)) =
      (specialIdeal W).map (renameEquiv (IsLocalRing.ResidueField O) σ) := by
  rw [map_renameEquiv_eq]
  unfold specialIdeal
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  refine RingHom.ext fun p => ?_
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, ren_apply, map_rename]
end GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
