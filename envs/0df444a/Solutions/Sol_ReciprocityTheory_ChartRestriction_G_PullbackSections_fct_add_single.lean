-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.fct_add_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:27:01.757984+00:00
-- url     : https://prove2.me/submissions/cdb92c0f-eedf-4c3a-a10d-a052f07ec0fe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped ContDiff
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (n : Fin 1 × Fin g →₀ ℕ) (p : Fin 1 × Fin g) :
    fct (n + Finsupp.single p 1) = fct n * ((n p : ℂ) + 1) := by
  unfold fct
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p),
    ← Finset.mul_prod_erase Finset.univ (fun q => (((n q).factorial : ℕ) : ℂ)) (Finset.mem_univ p)]
  have h1 : ∀ q ∈ Finset.univ.erase p,
      ((((n + Finsupp.single p 1 : Fin 1 × Fin g →₀ ℕ) q).factorial : ℕ) : ℂ) = ((n q).factorial : ℂ) := by
    intro q hq
    have hqp := Finset.ne_of_mem_erase hq
    simp [Finsupp.single_apply, hqp, Ne.symm hqp]
  rw [Finset.prod_congr rfl h1, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.G.PullbackSections
