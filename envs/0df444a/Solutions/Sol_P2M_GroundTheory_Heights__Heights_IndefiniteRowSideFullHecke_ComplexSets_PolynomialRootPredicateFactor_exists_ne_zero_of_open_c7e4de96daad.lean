-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_exists_ne_zero_of_open_c7e4de96daad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:31.458054+00:00
-- url     : https://prove2.me/submissions/67872211-fbf1-4517-bf64-2449de5494fe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolynomialRootPredicateFactor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PManifoldZerosComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolynomialRootPredicateFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Polynomial Filter Topology Classical
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialRootPredicateFactor
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialRootPredicateFactor
theorem _root_.solution {d : ℕ} {B : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} (hBc : Convex ℝ B)
    (hδ : AnalyticOnNhd ℂ δ B) {t₁ : Fin d → ℂ} (ht₁B : t₁ ∈ B) (ht₁ : δ t₁ ≠ 0) :
    ∀ V : Set (Fin d → ℂ), IsOpen V → V ⊆ B → V.Nonempty → ∃ t ∈ V, δ t ≠ 0 := by
  intro V hVo hVB ⟨v, hv⟩
  by_contra hall
  push Not at hall
  have h0 : δ =ᶠ[𝓝 v] 0 := Filter.eventually_of_mem (hVo.mem_nhds hv) hall
  exact ht₁ (hδ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hBc.isPreconnected (hVB hv) h0 ht₁B)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialRootPredicateFactor
