-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.TM.pderiv_tay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:30:30.774928+00:00
-- url     : https://prove2.me/submissions/bbeb4620-3918-4873-a855-f61aee7590fc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_mD_cons_deriv

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
theorem _root_.solution {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (j : Fin g) :
    pderiv ℂ ((0 : Fin 1), j) (tay θ 0) = tay (fun y => fderiv ℂ θ y (Pi.single j 1)) 0 := by
  ext n
  rw [MvPowerSeries.coeff_pderiv]
  show mD θ 0 (dirs (n + Finsupp.single ((0 : Fin 1), j) 1) + 0) / fct (n + Finsupp.single ((0 : Fin 1), j) 1) * ((n ((0 : Fin 1), j) : ℂ) + 1) =
    mD (fun y => fderiv ℂ θ y (Pi.single j 1)) 0 (dirs n + 0) / fct n
  have hd : dirs (n + Finsupp.single ((0 : Fin 1), j) 1) = (Pi.single j 1 : Fin g → ℂ) ::ₘ dirs n := by
    unfold dirs
    rw [Finsupp.toMultiset_add, Finsupp.toMultiset_single, one_nsmul, Multiset.map_add,
      Multiset.map_singleton, add_comm, Multiset.singleton_add]
  have hf : fct (n + Finsupp.single ((0 : Fin 1), j) 1) = fct n * ((n ((0 : Fin 1), j) : ℂ) + 1) := by
    unfold fct
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ((0 : Fin 1), j)),
      ← Finset.mul_prod_erase Finset.univ (fun p => ((n p).factorial : ℂ)) (Finset.mem_univ ((0 : Fin 1), j))]
    have hrest : ∏ x ∈ Finset.univ.erase ((0 : Fin 1), j), (((n + Finsupp.single ((0 : Fin 1), j) 1 : Fin 1 × Fin g →₀ ℕ) x).factorial : ℂ) =
        ∏ x ∈ Finset.univ.erase ((0 : Fin 1), j), ((n x).factorial : ℂ) := by
      refine Finset.prod_congr rfl fun x hx => ?_
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hx), add_zero]
    rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
    push_cast
    ring
  have hne : ((n ((0 : Fin 1), j) : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
  rw [add_zero, add_zero, hd, mD_cons_deriv hθ, hf, ← div_div, div_mul_cancel₀ _ hne]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
