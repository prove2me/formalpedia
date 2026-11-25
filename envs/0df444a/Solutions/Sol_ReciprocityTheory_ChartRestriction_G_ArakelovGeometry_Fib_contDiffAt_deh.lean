-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.contDiffAt_deh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:33:42.192875+00:00
-- url     : https://prove2.me/submissions/b5268b78-7e40-487a-b00b-5397e9481d70

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_contDiffAt_eval__5d0c5493ce4a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_deh_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → ι → ℂ) (e₀ : E) (i₀ : ι) (hg : ∀ i, ContDiffAt ℂ 1 (fun e => g e i) e₀)
    (h0 : g e₀ i₀ ≠ 0) (G : MvPolynomial ι ℤ) : ContDiffAt ℂ 1 (fun e => deh (g e) i₀ G) e₀ := by
  simp only [deh_apply]
  exact contDiffAt_eval₂ (fun e i => g e i / g e i₀) e₀ (fun i => (hg i).div (hg i₀) h0) G
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
