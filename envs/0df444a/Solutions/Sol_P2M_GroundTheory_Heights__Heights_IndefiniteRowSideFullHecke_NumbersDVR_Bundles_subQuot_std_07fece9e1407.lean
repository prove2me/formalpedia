-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_subQuot_std_07fece9e1407
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:05:26.607613+00:00
-- url     : https://prove2.me/submissions/18d3a8e7-5abf-4a8c-991e-1fd8b553e638

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ScaledRankOneLeStandardRankOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_mem_stdE_18e89a1870fc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_mem_standardRankOne_e1c44e101352
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_iSub_apply_a90d421cce72
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_qSub_apply_69ccb67ab979

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
theorem _root_.solution (x : (Σ k, ι k) → Ω) :
    IsSubQuot O x (stdE O x) iSub qSub (std1 O x) (std1 O x) := by
  refine ⟨?_, ?_, ?_, fun s _ => ⟨?_, ?_⟩⟩
  · intro v w h
    funext k
    fin_cases k
    simpa [iSub_apply] using congrFun h 0
  · intro w
    exact ⟨fun _ => w 0, by funext k; fin_cases k; rfl⟩
  · ext v
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨w, rfl⟩
      funext k
      simp [qSub_apply, iSub_apply]
    · intro h
      refine ⟨fun _ => v 0, ?_⟩
      funext j
      fin_cases j
      · simp [iSub_apply]
      · simpa [iSub_apply, qSub_apply] using (congrFun h 0).symm
  · ext v
    simp [AddSubgroup.mem_comap, mem_standardRankOne, mem_stdE, Fin.forall_fin_two, iSub_apply]
  · ext w
    rw [AddSubgroup.mem_map, mem_standardRankOne]
    constructor
    · intro h
      refine ⟨![0, w 0], (mem_stdE O).mpr ?_, ?_⟩
      · rw [Fin.forall_fin_two]
        simpa using h
      · funext k
        fin_cases k
        rfl
    · rintro ⟨v, hv, rfl⟩
      exact (mem_stdE O).mp hv 1
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
