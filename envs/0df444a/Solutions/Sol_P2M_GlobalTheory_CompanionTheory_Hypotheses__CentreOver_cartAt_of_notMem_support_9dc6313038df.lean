-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_of_notMem_support_9dc6313038df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:52:30.733163+00:00
-- url     : https://prove2.me/submissions/0765e2bd-81da-4ce3-a412-8220b265769e

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartierAtOfNotMemSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
theorem _root_.solution {X : Scheme.{0}} (J : X.IdealSheafData) (x : X) (hx : x ∉ J.support) :
    CartAt J x := by
  rw [Scheme.IdealSheafData.mem_support_iff] at hx
  push_neg at hx
  obtain ⟨U, hU⟩ := hx
  rw [Scheme.mem_zeroLocus_iff] at hU
  push_neg at hU
  obtain ⟨f, hf, hxf⟩ := hU
  refine ⟨X.affineBasicOpen f, 1, hxf, Submonoid.one_mem _, ?_⟩
  rw [Ideal.span_singleton_one, ← J.map_ideal_basicOpen U f]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hf)
    (X.toRingedSpace.isUnit_res_basicOpen f)
end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
