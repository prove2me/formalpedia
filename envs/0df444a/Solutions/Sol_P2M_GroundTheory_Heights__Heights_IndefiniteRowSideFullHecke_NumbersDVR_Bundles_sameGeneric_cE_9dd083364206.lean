-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_sameGeneric_cE_9dd083364206
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:29:50.097917+00:00
-- url     : https://prove2.me/submissions/6f3ad6d0-f4a8-44d9-b409-516888144d25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ScaledRankOneLeStandardRankOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_mem_stdE_18e89a1870fc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_mem_cE_628f0305f9d1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_cE_le_stdE_4add1758e388

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
theorem _root_.solution (x : (Σ k, ι k) → Ω) (c : O) (hc0 : c ≠ 0) (hc : algebraMap O Ω c ≠ 0) :
    SameGeneric O x (stdE O x) (cE O x c hc) := by
  intro s hs
  constructor
  · intro v hv
    rw [mem_stdE] at hv
    refine ⟨c, hc0, ?_⟩
    rw [mem_cE]
    have hcm := Subalgebra.algebraMap_mem (chartRing O (mseg x) s) c
    refine ⟨by simpa using mul_mem hcm (hv 0), ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    exact hv 1
  · intro v hv
    refine ⟨1, one_ne_zero, ?_⟩
    rw [map_one, one_smul]
    exact cE_le_stdE O x c hc s hs hv
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
