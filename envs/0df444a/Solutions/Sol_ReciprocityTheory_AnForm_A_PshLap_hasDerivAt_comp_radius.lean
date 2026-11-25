-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.hasDerivAt_comp_radius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:05:06.626367+00:00
-- url     : https://prove2.me/submissions/643fffaf-34b7-452b-bc2e-9e02ffb9c73d

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_hasDerivAt_circleMap_radius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {V : Set ℂ} {g : ℂ → ℝ} {G : ℂ → ℂ →L[ℝ] ℝ} {H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ}
namespace ReciprocityTheory.AnForm.A.PshLap
theorem _root_.solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : ℂ → F} {φ' : ℂ →L[ℝ] F} (r θ : ℝ) (h : HasFDerivAt φ φ' (circleMap 0 r θ)) :
    HasDerivAt (fun s : ℝ => φ (circleMap 0 s θ)) (φ' (circleMap 0 1 θ)) r :=
  h.comp_hasDerivAt (f := fun s : ℝ => circleMap 0 s θ) r (hasDerivAt_circleMap_radius r θ)
end ReciprocityTheory.AnForm.A.PshLap
