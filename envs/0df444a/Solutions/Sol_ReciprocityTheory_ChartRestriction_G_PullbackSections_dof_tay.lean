-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.dof_tay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:47:45.782447+00:00
-- url     : https://prove2.me/submissions/2f396f2d-45cc-49ea-b9ce-3aaf1a87a954

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_mD_cons_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_dof_addF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_coeff_tay
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_dirs_add_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_fct_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_fct_add_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_sum_single_smul

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
theorem _root_.solution {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (v : Fin g → ℂ) (s : Multiset (Fin g → ℂ)) :
    Dof (addF ℂ g) v (tay θ s) = tay θ (v ::ₘ s) := by
  classical
  rw [dof_addF]
  ext n
  have key : ∀ j : Fin g, coeff n (C (v j) * pderiv ℂ ((0 : Fin 1), j) (tay θ s)) =
      v j * mD θ 0 (Pi.single j 1 ::ₘ (dirs n + s)) / fct n := by
    intro j
    have h1 : ((n ((0 : Fin 1), j) : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
    have h2 := fct_ne_zero n
    rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_pderiv, coeff_tay, dirs_add_single, fct_add_single,
      Multiset.cons_add]
    push_cast
    field_simp
  rw [map_sum, Finset.sum_congr rfl fun j _ => key j, coeff_tay, Multiset.add_cons]
  have hs := mD_cons_sum hθ Finset.univ v (fun j => (Pi.single j (1 : ℂ) : Fin g → ℂ)) (dirs n + s)
  rw [← sum_single_smul v] at hs
  rw [hs, Finset.sum_div]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
