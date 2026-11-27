-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagRatioBasis_proof_f83996677b7d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:01:49.008279+00:00
-- url     : https://prove2.me/submissions/c30fd74a-7602-42e6-8ab0-e9e3e757b819

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StDiagRatioBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagRatioBasis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_coneRatios_wwCoord_diag_57e514729342

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace DiagRatioBasis
theorem _root_.solution (hY : YYRatioBasis.Statement) : DiagRatioBasis.Statement := by
  intro Ω _ _ ι ν κ _ _ _ E _ _ Φ _ _ _ x e b φ δ g i₀ l₀ k₀ k₁ d t a hx ht htF htA hδ hδF hφ hgF hg ha
  obtain ⟨c, t', hc, hind, hmem, halg⟩ :=
    hY Ω ι ν κ E Φ x e b φ δ g i₀ l₀ k₀ k₁ d t a hx ht htF htA hδ hδF hφ hgF hg ha
  refine ⟨diagChart c, t', fun k => ?_, hind, ?_, ?_⟩
  · cases k
    exacts [hc .base, hc .det, hc .line, hc .line]
  · rw [coneRatios_wwCoord_diag]; exact hmem
  · rw [coneRatios_wwCoord_diag]; exact halg
end DiagRatioBasis
end GroundTheory.Heights₂.Heights.Inter
