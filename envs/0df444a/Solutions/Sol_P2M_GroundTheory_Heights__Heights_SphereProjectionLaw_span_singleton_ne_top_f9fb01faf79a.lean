-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_span_singleton_ne_top_f9fb01faf79a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:19:10.848122+00:00
-- url     : https://prove2.me/submissions/0c3607d3-17e0-4f98-9547-16e06d2e32ef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereProjectionLaw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.SphereProjectionLaw
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.SphereProjectionLaw
theorem _root_.solution {N : ℕ} (hN : 2 ≤ N) (p : Fin N → ℂ) :
    Submodule.span ℂ {p} ≠ ⊤ := by
  intro h
  have h1 := finrank_span_le_card (R := ℂ) ({p} : Set (Fin N → ℂ))
  rw [h, finrank_top, Module.finrank_fin_fun] at h1
  simp at h1
  omega
end GroundTheory.Heights₂.Heights.SphereProjectionLaw
