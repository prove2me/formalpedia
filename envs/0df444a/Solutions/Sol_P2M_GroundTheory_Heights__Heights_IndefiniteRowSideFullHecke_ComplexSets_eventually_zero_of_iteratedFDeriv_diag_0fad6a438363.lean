-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eventually_zero_of_iteratedFDeriv_diag_0fad6a438363
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:35.289614+00:00
-- url     : https://prove2.me/submissions/27ae3b9e-66ec-4178-b21a-bdeb026f9a89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticImplicitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularLocusDense

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
open Topology Filter Module
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {ψ : E → ℂ} {y₀ : E} (hψ : AnalyticAt ℂ ψ y₀)
    (h0 : ∀ (n : ℕ) (v : E), iteratedFDeriv ℂ n ψ y₀ (fun _ => v) = 0) :
    ∀ᶠ u in 𝓝 y₀, ψ u = 0 := by
  obtain ⟨p, r, hp⟩ := hψ
  filter_upwards [Metric.eball_mem_nhds y₀ hp.r_pos] with u hu
  have hmem : u - y₀ ∈ Metric.eball (0 : E) r := by
    simpa [Metric.mem_eball, edist_eq_enorm_sub] using hu
  have hs := hp.hasSum_iteratedFDeriv hmem
  simp only [h0, smul_zero, add_sub_cancel] at hs
  exact hs.unique hasSum_zero
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
