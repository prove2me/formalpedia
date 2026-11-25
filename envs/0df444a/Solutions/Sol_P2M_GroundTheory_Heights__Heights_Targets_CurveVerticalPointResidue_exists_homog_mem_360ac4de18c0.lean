-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_exists_homog_mem_360ac4de18c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:00:58.1719+00:00
-- url     : https://prove2.me/submissions/b6dc84cf-5fda-4a0e-8477-9e29ad79ac1c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertIndexSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointResidue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_isMultiHomog_add__e001087792f4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_exists_homog_b690ef546a3c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_coordProd_8cb4f1e2e87b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_mul_92fa4aba8533
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_isMultiHomog_add__036135b665a7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_mul_0d39b8f19b1f
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_coordProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_mul


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
    (hχ : ∀ k, χ (X ⟨k, c k⟩) = 1) {W : Ideal (MRing ι)} (hW : IsMultiHomogIdeal W)
    {f : MRing ι} (hf : f ∈ W) :
    ∃ (n : K → ℕ) (G : MRing ι), G ∈ W ∧ IsMultiHomog G n ∧ χ G = χ f := by
  classical
  have hχp : ∀ n : K → ℕ, χ (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n k) = 1 := fun n => by
    simp [map_prod, hχ]
  obtain ⟨Sg, hSg, rfl⟩ := hW
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hSg x hx
    exact ⟨a, x, Ideal.subset_span hx, ha, rfl⟩
  | zero => exact ⟨0, 0, zero_mem _, fun m hm => absurd hm (by simp), rfl⟩
  | add x z _ _ hx hz =>
    obtain ⟨n₁, G₁, hG₁, h₁, e₁⟩ := hx
    obtain ⟨n₂, G₂, hG₂, h₂, e₂⟩ := hz
    refine ⟨n₁ + n₂, G₁ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n₂ k + G₂ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n₁ k,
      add_mem (Ideal.mul_mem_right _ _ hG₁) (Ideal.mul_mem_right _ _ hG₂),
      isMultiHomog_add' (isMultiHomog_mul h₁ (isMultiHomog_coordProd c n₂)) ?_, ?_⟩
    · rw [add_comm n₁]
      exact isMultiHomog_mul h₂ (isMultiHomog_coordProd c n₁)
    · rw [map_add, map_mul, map_mul, hχp, hχp, mul_one, mul_one, e₁, e₂, map_add]
  | smul a x _ hx =>
    obtain ⟨n, G, hG, h, e⟩ := hx
    obtain ⟨m, A, hA, eA⟩ := exists_homog χ c hχ a
    refine ⟨m + n, A * G, Ideal.mul_mem_left _ _ hG, isMultiHomog_mul hA h, ?_⟩
    rw [smul_eq_mul, map_mul, map_mul, eA, e]
end GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue
