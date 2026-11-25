-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GI.prodG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:48.13934+00:00
-- url     : https://prove2.me/submissions/76297fe9-9650-4ea1-9d21-c48feac25dc0

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_NormMono
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GI_cplx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G PositivityTheory.Rg.Sw.WR.G.GI
open PositivityTheory.Rg.Sw
namespace PositivityTheory.Rg.Sw.WR.G.GI
theorem _root_.solution (m n : ℕ) (c : ℝ) (hc : 0 < c) (D : Fin m → Fin n → ℕ) :
    Integrable fun x : Fin m → Fin n → ℂ => ∏ a, ∏ i, (‖x a i‖ ^ D a i * Real.exp (-c * ‖x a i‖ ^ 2)) := by
  refine Integrable.fintype_prod (f := fun a (r : Fin n → ℂ) => ∏ i, (‖r i‖ ^ D a i * Real.exp (-c * ‖r i‖ ^ 2)))
    (μ := fun _ => volume) (fun a => ?_)
  exact Integrable.fintype_prod (f := fun i (z : ℂ) => ‖z‖ ^ D a i * Real.exp (-c * ‖z‖ ^ 2))
    (μ := fun _ => volume) (fun i => cplx c hc _)
end PositivityTheory.Rg.Sw.WR.G.GI
