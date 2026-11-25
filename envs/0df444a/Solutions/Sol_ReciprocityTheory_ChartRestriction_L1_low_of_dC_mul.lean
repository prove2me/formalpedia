-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.low_of_dC_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:41:14.801905+00:00
-- url     : https://prove2.me/submissions/a4214927-b37a-4cff-8172-42e8345cf97c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_coeff_mul_low
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_exists_dC_inv

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
theorem _root_.solution (H : PowerSeries ℂ) (n0 : ℕ) (u : ℂ) (hu : u ≠ 0)
    (h0 : ∀ n < n0, PowerSeries.coeff n (dC * H) = 0) (h1 : PowerSeries.coeff n0 (dC * H) = u) :
    ∃ k, n0 = k + 1 ∧ (∀ n < k, PowerSeries.coeff n H = 0) ∧ PowerSeries.coeff k H = u := by
  obtain ⟨v, hv0, hv⟩ := exists_dC_inv
  have hV : PowerSeries.coeff 0 (v.map (Int.castRingHom ℂ)) = 1 := by
    rw [PowerSeries.coeff_map, hv0, map_one]
  obtain ⟨hlow, hn0⟩ := coeff_mul_low _ _ hV n0 h0
  rw [h1, ← hv H] at hn0
  rw [← hv H] at hlow
  rcases n0 with _ | k
  · rw [PowerSeries.coeff_zero_X_mul] at hn0
    exact absurd hn0.symm hu
  · refine ⟨k, rfl, fun n hn => ?_, ?_⟩
    · rw [← PowerSeries.coeff_succ_X_mul]
      exact hlow _ (by omega)
    · rw [← PowerSeries.coeff_succ_X_mul]
      exact hn0
end ReciprocityTheory.ChartRestriction.L1
