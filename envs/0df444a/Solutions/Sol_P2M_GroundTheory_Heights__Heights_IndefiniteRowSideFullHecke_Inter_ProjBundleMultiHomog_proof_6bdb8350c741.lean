-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ProjBundleMultiHomog_proof_6bdb8350c741
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:58:50.955974+00:00
-- url     : https://prove2.me/submissions/851becbd-b043-47ca-980c-90608c40cd72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_component_mem_ker_genMap_74104e2fa659
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_isMultiHomogIdeal_iff_08bad36ad538
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_isMultiHomog_iff_c75df70a60fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_homog_span_60f094fec41c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ker_genMap_le_7f717af17469


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace ProjBundleMultiHomog
theorem _root_.solution : ProjBundleMultiHomog.Statement := by
  intro K _ ι _ N1 t n P d c m B hP hQ hB
  classical
  obtain ⟨-, ⟨hPp, hPh, -⟩, -, -⟩ := hP
  have := hPp
  have hPc := (Bridge.isMultiHomogIdeal_iff P).mpr hPh
  obtain ⟨S, _, V, γ, hV, hVker, hBspan⟩ := exists_homog_span P hPc c m
    (fun r j => (Bridge.isMultiHomog_iff _ _).mpr (hQ.1 r j)) B
    (fun a => by rw [← hB.2]; exact Submodule.subset_span ⟨a, rfl⟩)
  have hker : projBundleIdeal P B = RingHom.ker (genMap P fun s j => toFn P (V s j)) :=
    le_antisymm (ker_genMap_le P B _ fun s => by rw [hB.2]; exact hVker s)
      (ker_genMap_le P _ B hBspan)
  rw [hker]
  obtain ⟨G, hG, hPG⟩ := hPh
  exact (Bridge.isMultiHomogIdeal_iff _).mp fun f hf b => component_mem_ker_genMap P G hG hPG V γ hV hf b
end ProjBundleMultiHomog
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
