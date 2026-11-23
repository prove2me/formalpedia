-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.zetaC_pow_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:50.358139+00:00
-- url     : https://prove2.me/submissions/92a24239-071c-43a5-a86e-540d100a13a8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic

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
theorem _root_.solution {m : ℕ} (hm : 0 < m) : zetaC m ^ m = 1 := by
  unfold zetaC
  rw [← Complex.exp_nat_mul]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have : (m : ℂ) * (2 * Real.pi * Complex.I / m) = 2 * Real.pi * Complex.I := by field_simp
  rw [this, Complex.exp_two_pi_mul_I]
end ReciprocityTheory.ChartRestriction.L1
