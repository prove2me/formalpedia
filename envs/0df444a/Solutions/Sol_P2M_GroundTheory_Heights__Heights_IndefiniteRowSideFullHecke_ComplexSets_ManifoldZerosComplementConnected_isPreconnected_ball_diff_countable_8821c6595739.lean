-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_ball_diff_countable_8821c6595739
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:08.876414+00:00
-- url     : https://prove2.me/submissions/e027bca0-cb8e-424a-8b88-f1d8a724eb6f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StManifoldZerosComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PManifoldZerosComplementConnected

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
    [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : 1 < Module.rank ℝ E) (c : E) {r : ℝ} (hr : 0 < r)
    {s : Set E} (hs : s.Countable) : IsPreconnected (Metric.ball c r \ s) := by
  let e : OpenPartialHomeomorph E E := OpenPartialHomeomorph.univBall c r
  have hsrc : e.source = univ := OpenPartialHomeomorph.univBall_source c r
  have htgt : e.target = Metric.ball c r := OpenPartialHomeomorph.univBall_target c hr
  have hc : (e ⁻¹' s).Countable := hs.preimage_of_injOn (e.injOn.mono (by rw [hsrc]; exact subset_univ _))
  have hcont : ContinuousOn e univ := hsrc ▸ e.continuousOn
  have heq : e '' (e ⁻¹' s)ᶜ = Metric.ball c r \ s := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨htgt ▸ e.map_source (hsrc ▸ mem_univ v), hv⟩
    · rintro ⟨hw, hws⟩
      rw [← htgt] at hw
      exact ⟨e.symm w, by simpa [mem_compl_iff, mem_preimage, e.right_inv hw] using hws, e.right_inv hw⟩
  rw [← heq]
  exact (hc.isConnected_compl_of_one_lt_rank hE).isPreconnected.image e (hcont.mono (subset_univ _))
end ManifoldZerosComplementConnected
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
