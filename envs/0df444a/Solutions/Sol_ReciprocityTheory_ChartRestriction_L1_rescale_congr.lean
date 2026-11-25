-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.rescale_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:39:25.09479+00:00
-- url     : https://prove2.me/submissions/05942297-6628-4454-9467-ef2d55fddb6e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {p : ℕ} (hp : 0 < p) (b : ℕ) (f : PowerSeries ℤ) :
    ∃ w : PowerSeries ℂ, CoeffIn (Rm p) w ∧
      PowerSeries.rescale (zetaC p ^ b) (f.map (Int.castRingHom ℂ)) =
        f.map (Int.castRingHom ℂ) + PowerSeries.C (1 - zetaC p) * w := by
  refine ⟨PowerSeries.mk fun n => -(∑ i ∈ Finset.range (b * n), zetaC p ^ i) * ((PowerSeries.coeff n f : ℤ) : ℂ), ?_, ?_⟩
  · intro n
    rw [PowerSeries.coeff_mk]
    exact mul_mem (neg_mem (sum_mem fun i _ => pow_mem (Subring.subset_closure (Set.mem_singleton _)) _))
      (intCast_mem _ _)
  · ext n
    simp only [map_add, PowerSeries.coeff_rescale, PowerSeries.coeff_map, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mk, eq_intCast]
    have hg := geom_sum_mul (zetaC p) (b * n)
    linear_combination (-((PowerSeries.coeff n f : ℤ) : ℂ)) * hg
end ReciprocityTheory.ChartRestriction.L1
