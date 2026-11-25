-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_eq_zero_of_dense_5cad5f3be74c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:32:03.855835+00:00
-- url     : https://prove2.me/submissions/79b74be1-c4d2-4c52-b691-eb504a33926f

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
theorem _root_.solution {d : ℕ} {B : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} (hBo : IsOpen B)
    (hdense : ∀ V : Set (Fin d → ℂ), IsOpen V → V ⊆ B → V.Nonempty → ∃ t ∈ V, δ t ≠ 0)
    {g : (Fin d → ℂ) → ℂ} {t : Fin d → ℂ} (ht : t ∈ B) (hg : ContinuousAt g t)
    (hz : ∀ s ∈ B, δ s ≠ 0 → g s = 0) : g t = 0 := by
  by_contra h
  obtain ⟨W, hW, hWo, htW⟩ := mem_nhds_iff.1 (hg.eventually_ne h)
  obtain ⟨s, ⟨hsW, hsB⟩, hs⟩ := hdense (W ∩ B) (hWo.inter hBo) Set.inter_subset_right ⟨t, htW, ht⟩
  exact hW hsW (hz s hsB hs)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialRootPredicateFactor
