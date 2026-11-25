-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_contDiffAt_eval__5d0c5493ce4a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:57:45.090402+00:00
-- url     : https://prove2.me/submissions/7db6d26f-a517-46b9-a86a-5387ec2a86ec

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB

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
    (g : E → ι → ℂ) (e₀ : E) (hg : ∀ i, ContDiffAt ℂ 1 (fun e => g e i) e₀)
    (G : MvPolynomial ι ℤ) : ContDiffAt ℂ 1 (fun e => eval₂ (Int.castRingHom ℂ) (g e) G) e₀ := by
  induction G using MvPolynomial.induction_on
  next r =>
    simp only [eval₂_C]
    exact contDiffAt_const
  next p q hp hq =>
    simp only [eval₂_add]
    exact hp.add hq
  next p i hp =>
    simp only [eval₂_mul, eval₂_X]
    exact hp.mul (hg i)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
