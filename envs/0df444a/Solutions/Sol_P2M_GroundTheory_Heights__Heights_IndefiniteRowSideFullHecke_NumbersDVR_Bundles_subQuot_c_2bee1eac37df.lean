-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_subQuot_c_2bee1eac37df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:06:31.783385+00:00
-- url     : https://prove2.me/submissions/c977b4b3-9731-40dd-adf6-0f4b13b46e46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ScaledRankOneLeStandardRankOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_mem_cE_628f0305f9d1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_mem_standardRankOne_e1c44e101352
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_mem_scaledRankOne_7d4f94ad393c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_iSub_apply_a90d421cce72
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_subQuot_std_07fece9e1407

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
theorem _root_.solution (x : (Σ k, ι k) → Ω) (c : O) (hc : algebraMap O Ω c ≠ 0) :
    IsSubQuot O x (cE O x c hc) iSub qSub (std1 O x) (sc1 O x c hc) := by
  refine ⟨(subQuot_std O x).1, (subQuot_std O x).2.1, (subQuot_std O x).2.2.1, fun s _ => ⟨?_, ?_⟩⟩
  · ext v
    simp [AddSubgroup.mem_comap, mem_standardRankOne, mem_cE, iSub_apply]
  · ext w
    rw [AddSubgroup.mem_map, mem_scaledRankOne]
    constructor
    · intro h
      refine ⟨![0, w 0], (mem_cE O).mpr ⟨by simp, by simpa using h⟩, ?_⟩
      funext k
      fin_cases k
      rfl
    · rintro ⟨v, hv, rfl⟩
      exact ((mem_cE O).mp hv).2
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
