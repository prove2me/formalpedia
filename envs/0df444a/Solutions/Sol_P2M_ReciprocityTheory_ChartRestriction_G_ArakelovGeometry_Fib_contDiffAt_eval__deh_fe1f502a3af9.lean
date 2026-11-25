-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_contDiffAt_eval__deh_fe1f502a3af9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:40.852926+00:00
-- url     : https://prove2.me/submissions/86803266-95e4-4bef-8fc1-5b50ed87c7b7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_contDiffAt_deh

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
    (g : E → ι → ℂ) (t : E → ℂ) (e₀ : E) (i₀ : ι) (hg : ∀ i, ContDiffAt ℂ 1 (fun e => g e i) e₀)
    (ht : ContDiffAt ℂ 1 t e₀) (h0 : g e₀ i₀ ≠ 0) (H : Polynomial (MvPolynomial ι ℤ)) :
    ContDiffAt ℂ 1 (fun e => H.eval₂ (deh (g e) i₀) (t e)) e₀ := by
  refine Polynomial.induction_on' H (fun p q hp hq => ?_) (fun n a => ?_)
  · simp only [Polynomial.eval₂_add]
    exact hp.add hq
  · simp only [Polynomial.eval₂_monomial]
    exact (contDiffAt_deh g e₀ i₀ hg h0 a).mul (ht.pow n)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
