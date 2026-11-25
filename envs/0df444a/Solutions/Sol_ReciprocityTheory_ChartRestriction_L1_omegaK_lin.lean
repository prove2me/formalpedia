-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.omegaK_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:38:18.013517+00:00
-- url     : https://prove2.me/submissions/24618bf5-ec84-4b70-9480-1878d175d3b1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModCMPoint

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
theorem _root_.solution {d : ℕ} (hd : 0 < d) {t n : ℤ} (h : (t : ℂ) * omegaK d + n = 0) :
    t = 0 ∧ n = 0 := by
  have h2 : (t : ℂ) * (1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) + 2 * n = 0 := by
    rw [omegaK] at h
    linear_combination 2 * h
  have hsq : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have h3 : (((t : ℝ) + 2 * n : ℝ) : ℂ) + (((t : ℝ) * Real.sqrt d : ℝ) : ℂ) * Complex.I = 0 := by
    push_cast
    linear_combination h2
  have him : (t : ℝ) * Real.sqrt d = 0 := by
    have := congrArg Complex.im h3
    simpa using this
  have hre : (t : ℝ) + 2 * n = 0 := by
    have := congrArg Complex.re h3
    simpa using this
  have ht : (t : ℝ) = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · exact absurd h hsq.ne'
  have hn : (n : ℝ) = 0 := by linarith
  exact ⟨by exact_mod_cast ht, by exact_mod_cast hn⟩
end ReciprocityTheory.ChartRestriction.L1
