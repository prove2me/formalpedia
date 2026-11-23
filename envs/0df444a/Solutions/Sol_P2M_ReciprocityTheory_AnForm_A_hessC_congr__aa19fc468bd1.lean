-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_A_hessC_congr__aa19fc468bd1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:11.853433+00:00
-- url     : https://prove2.me/submissions/157f7ca6-ae16-404b-b42a-3f52496f2770

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Complex Filter Topology
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {φ ψ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (h : φ =ᶠ[𝓝 z] ψ) :
    hessC φ z = hessC ψ z := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ :=
    h.eventuallyEq_nhds.mono fun y hy => hy.fderiv_eq
  have h2 : fderiv ℝ (fderiv ℝ φ) z = fderiv ℝ (fderiv ℝ ψ) z := h1.fderiv_eq
  ext i j
  simp only [hessC, h2]
end ReciprocityTheory.AnForm.A
