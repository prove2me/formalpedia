-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_quotIso_c_2c1f16a9e819
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:58:55.561558+00:00
-- url     : https://prove2.me/submissions/cd4d95ac-589d-48ca-b55a-fa7af74260d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ScaledRankOneLeStandardRankOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_frameBundle_lat_2faeb195af08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_mem_standardRankOne_e1c44e101352
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_mem_scaledRankOne_7d4f94ad393c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_mem_graph_837a355538f3

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
    QuotIso O x (std1 O x) (sc1 O x c hc) (std1 O x) (sc1 O x c hc) := by
  have hcm : ∀ s, algebraMap O Ω c ∈ chartRing O (mseg x) s := fun s =>
    Subalgebra.algebraMap_mem _ c
  refine ⟨frameBundle O (mseg x) (bGraph (algebraMap O Ω c) hc), fun s _ => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro v
    rw [frameBundle_lat, mem_graph, mem_scaledRankOne]
    simp
  · intro v
    rw [mem_standardRankOne]
    constructor
    · rintro ⟨w, hw⟩
      rw [frameBundle_lat, mem_graph] at hw
      have h := add_mem (mul_mem (hcm s) hw.1) hw.2
      rwa [← mul_assoc, mul_inv_cancel₀ hc, one_mul, sub_add_cancel] at h
    · intro hv
      refine ⟨v, ?_⟩
      rw [frameBundle_lat, mem_graph]
      simp [hv]
  · intro w
    rw [frameBundle_lat, mem_graph, mem_scaledRankOne]
    constructor
    · rintro ⟨h1, _⟩
      simpa using neg_mem h1
    · intro h
      refine ⟨by simpa using neg_mem h, ?_⟩
      have h2 := mul_mem (hcm s) h
      rwa [← mul_assoc, mul_inv_cancel₀ hc, one_mul] at h2
  · intro w
    rw [mem_standardRankOne]
    constructor
    · rintro ⟨v, hv⟩
      rw [frameBundle_lat, mem_graph] at hv
      exact hv.2
    · intro hw
      refine ⟨w, ?_⟩
      rw [frameBundle_lat, mem_graph]
      simp [hw]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
