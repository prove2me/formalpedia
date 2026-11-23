-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.norm_prime_pos_complexPadic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:34.740861+00:00
-- url     : https://prove2.me/submissions/9cbc56d0-bd80-4165-a286-b658f0d28633

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsPowerMulUnitNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
private theorem norm_natCast_l_padicComplex_eq_inv : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends (p := l) ((l : ℚ_[l]) : PadicAlgCl l)
  rw [PadicAlgCl.norm_extends, Padic.norm_p] at h
  have e : (((l : ℚ_[l]) : PadicAlgCl l) : ℂ_[l]) = (l : ℂ_[l]) := by simp
  rw [e] at h
  exact h
end ReciprocityTheory.ChartRestriction.L1
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution : 0 < ‖(l : ℂ_[l])‖ := by
  rw [norm_natCast_l_padicComplex_eq_inv l]
  exact inv_pos.mpr (by exact_mod_cast (Fact.out : Nat.Prime l).pos)
end ReciprocityTheory.ChartRestriction.L1
