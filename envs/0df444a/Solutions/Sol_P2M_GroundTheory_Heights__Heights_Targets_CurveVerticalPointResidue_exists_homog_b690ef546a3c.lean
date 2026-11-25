-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_exists_homog_b690ef546a3c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:40:43.236545+00:00
-- url     : https://prove2.me/submissions/9d5d3555-7b3f-49e0-bf38-9d427b9a5e2c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertIndexSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointResidue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_isMultiHomog_add__e001087792f4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_isMultiHomog_C__1f6a8b4f0c11
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_X_cf870dae9c4f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_coordProd_8cb4f1e2e87b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_mul_92fa4aba8533
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_isMultiHomog_add__036135b665a7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_mul_0d39b8f19b1f
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_coordProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isMultiHomog_X


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Inter.AvoidRing
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue
theorem _root_.solution {S : Type*} [CommRing S] (χ : MRing ι →+* S) (c : ∀ k, ι k)
    (hχ : ∀ k, χ (X ⟨k, c k⟩) = 1) (f : MRing ι) :
    ∃ (n : K → ℕ) (G : MRing ι), IsMultiHomog G n ∧ χ G = χ f := by
  classical
  have hχp : ∀ n : K → ℕ, χ (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n k) = 1 := fun n => by
    simp [map_prod, hχ]
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, isMultiHomog_C' a, rfl⟩
  | add p q hp hq =>
    obtain ⟨n₁, G₁, h₁, e₁⟩ := hp
    obtain ⟨n₂, G₂, h₂, e₂⟩ := hq
    refine ⟨n₁ + n₂, G₁ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n₂ k + G₂ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n₁ k,
      isMultiHomog_add' (isMultiHomog_mul h₁ (isMultiHomog_coordProd c n₂)) ?_, ?_⟩
    · rw [add_comm n₁]
      exact isMultiHomog_mul h₂ (isMultiHomog_coordProd c n₁)
    · rw [map_add, map_mul, map_mul, hχp, hχp, mul_one, mul_one, e₁, e₂, map_add]
  | mul_X p i hp =>
    obtain ⟨n, G, h, e⟩ := hp
    exact ⟨n + Pi.single i.1 1, G * X i, isMultiHomog_mul h (isMultiHomog_X i.1 i.2), by
      rw [map_mul, map_mul, e]⟩
end GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue
