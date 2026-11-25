-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_convex_inter_ne_zero_5a3afb509677
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:49.560559+00:00
-- url     : https://prove2.me/submissions/f167e342-cd5d-46d6-9d67-766b45ecbf7d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StManifoldZerosComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PManifoldZerosComplementConnected
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_inter_ne_zero_of_complex_4bc36446fe62

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
open Topology Filter Set
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace ManifoldZerosComplementConnected
theorem _root_.solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} (hUo : IsOpen U) (hUc : Convex ℝ U)
    {f : E → ℂ} (hf : AnalyticOnNhd ℂ f U) : IsPreconnected (U ∩ {z | f z ≠ 0}) := by
  refine isPreconnected_of_forall_pair ?_
  rintro p ⟨hpU, hp⟩ q ⟨hqU, hq⟩
  let ℓ : ℂ → E := fun t => p + t • (q - p)
  have hℓc : Continuous ℓ := by fun_prop
  have hℓa : ∀ t, AnalyticAt ℂ ℓ t := fun t =>
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hVo : IsOpen (ℓ ⁻¹' U) := hUo.preimage hℓc
  have hVc : Convex ℝ (ℓ ⁻¹' U) := by
    intro a ha b hb s t hs ht hst
    have hmem := hUc ha hb hs ht hst
    show ℓ (s • a + t • b) ∈ U
    convert hmem using 1
    obtain rfl : t = 1 - s := by linarith
    simp only [ℓ, ← Complex.coe_smul]
    push_cast
    module
  have h0 : (0 : ℂ) ∈ ℓ ⁻¹' U := by simpa [ℓ] using hpU
  have h1 : (1 : ℂ) ∈ ℓ ⁻¹' U := by simpa [ℓ] using hqU
  refine ⟨ℓ '' (ℓ ⁻¹' U ∩ {t | f (ℓ t) ≠ 0}), ?_, ⟨0, ⟨h0, by simpa [ℓ] using hp⟩, by simp [ℓ]⟩,
    ⟨1, ⟨h1, by simpa [ℓ] using hq⟩, by simp [ℓ]⟩, ?_⟩
  · rintro _ ⟨t, ⟨htV, ht⟩, rfl⟩
    exact ⟨htV, ht⟩
  · exact (ManifoldZerosComplementConnected.isPreconnected_inter_ne_zero_of_complex hVo
      hVc.isPreconnected (φ := fun t => f (ℓ t)) (fun t ht => (hf (ℓ t) ht).comp (hℓa t)) h0
      (by simpa [ℓ] using hp)).image ℓ hℓc.continuousOn
end ManifoldZerosComplementConnected
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
