-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_trdeg_blocks_le_1e793719e155
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:21:16.114852+00:00
-- url     : https://prove2.me/submissions/6bbe1749-ac9a-4146-a8bc-2c7b74fa2e75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagProjSpecialDimSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosureModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PAdjoinTrdegAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosurePullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagProjTrdegLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_trdeg_quot_ker_eq_range_ea734c1d0c2f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_rename_comp_pointConeMap_7ec05c7ad4fe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagProjTrdegLe
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagProjTrdegLe
theorem _root_.solution {O Φ : Type} [CommRing O] [Field Φ] [Algebra O Φ] {Λ K' : Type} (ι' : Λ → Type)
    (j : K' ↪ Λ) (pt : (Σ o, ι' o) → Φ) :
    Algebra.trdeg O (MvPolynomial (Σ o, ι' (j o)) O ⧸ pointIdeal O (fun p => pt (FieldNumbers.blockIncl j ι' p))) ≤
      Algebra.trdeg O (MvPolynomial (Σ o, ι' o) O ⧸ pointIdeal O pt) := by
  have hren : Function.Injective ((rename j : MvPolynomial K' Φ →ₐ[Φ] MvPolynomial Λ Φ).restrictScalars O) :=
    rename_injective _ j.injective
  rw [pointIdeal, pointIdeal, trdeg_quot_ker_eq_range _ _ hren,
    trdeg_quot_ker_eq_range (pointConeMap O pt) (AlgHom.id O _) (fun _ _ h => h), rename_comp_pointConeMap,
    AlgHom.id_comp]
  exact trdeg_le_of_injective (Subalgebra.inclusion (AlgHom.range_comp_le_range _ _))
    (Subalgebra.inclusion_injective _)
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagProjTrdegLe
