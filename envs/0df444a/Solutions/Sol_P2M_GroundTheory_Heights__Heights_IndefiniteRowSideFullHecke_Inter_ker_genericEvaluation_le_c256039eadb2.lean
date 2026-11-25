-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ker_genericEvaluation_le_c256039eadb2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:05.352098+00:00
-- url     : https://prove2.me/submissions/3ac2e5d4-c1a9-4341-8960-bfdcaa2540eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_sumAlgEquiv_rename_inr_97418c89fc9c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ker_toFn_0318e751caee


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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {S : Type} [Fintype S]
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype S]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution (P : Ideal (MRing ι)) :
    RingHom.ker (genericEvaluation (S := S) P) ≤ Ideal.map (rename Sum.inr) P := by
  intro f hf
  set e := sumAlgEquiv ℤ S (Σ k, ι k)
  have hg : e f ∈ Ideal.map (C : MRing ι →+* MvPolynomial S (MRing ι)) P := by
    rw [← ker_toFn P, ← MvPolynomial.ker_map]
    exact hf
  have hre : ∀ x : MRing ι, e.symm (C x) = rename Sum.inr x := by
    intro x
    rw [AlgEquiv.symm_apply_eq]
    exact (sumAlgEquiv_rename_inr x).symm
  have h1 : Ideal.map e.symm (Ideal.map (C : MRing ι →+* MvPolynomial S (MRing ι)) P) ≤
      Ideal.map (rename Sum.inr) P := by
    rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap, hre]
    exact Ideal.mem_map_of_mem _ hx
  simpa using h1 (Ideal.mem_map_of_mem e.symm hg)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
