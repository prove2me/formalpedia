-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_exists_ne_zero_of_open_fbf002cb46b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:06:41.213274+00:00
-- url     : https://prove2.me/submissions/0738c44e-9a37-4dba-a21c-1f4aa75e205a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetPieceProductAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedFibreSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetPieceProductAnalytic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_tailL_cons_a65dbe17d6c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_cons_tailL_bc1d6b87226f

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
open Topology Metric Filter
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SheetPieceProductAnalytic
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SheetPieceProductAnalytic
theorem _root_.solution {d : ℕ} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ}
    (hδ : AnalyticOnNhd ℂ δ D) (hD : IsPreconnected D) (hne : ∃ y ∈ D, δ y ≠ 0)
    (V : Set (Fin (d + 1) → ℂ)) (hV : IsOpen V) (hVW : V ⊆ tailL d ⁻¹' D) (hVne : V.Nonempty) :
    ∃ p ∈ V, δ (tailL d p) ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨p, hp⟩ := hVne
  have hc : Continuous fun y : Fin d → ℂ => (Fin.cons (p 0) y : Fin (d + 1) → ℂ) := by
    refine continuous_pi fun i => ?_
    cases i using Fin.cases
    · simpa using continuous_const
    · simpa using continuous_apply _
  have hev : δ =ᶠ[𝓝 (tailL d p)] 0 := by
    have hmem : (fun y : Fin d → ℂ => (Fin.cons (p 0) y : Fin (d + 1) → ℂ)) ⁻¹' V ∈ 𝓝 (tailL d p) := by
      refine hc.continuousAt.preimage_mem_nhds ?_
      show V ∈ 𝓝 (Fin.cons (p 0) (tailL d p) : Fin (d + 1) → ℂ)
      rw [cons_tailL]
      exact hV.mem_nhds hp
    filter_upwards [hmem] with y hy
    have := h _ hy
    rwa [tailL_cons] at this
  obtain ⟨y, hy, hy0⟩ := hne
  exact hy0 (hδ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hD (hVW hp) hev hy)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SheetPieceProductAnalytic
