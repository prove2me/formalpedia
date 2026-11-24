-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kq_int_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:47:23.887535+00:00
-- url     : https://prove2.me/submissions/70af34de-e342-479c-a50a-85aa14b2219b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurNewton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormSqrtNegPowPrimeSqSub
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
private theorem kq_intnorm_lemma (n : ℤ) : ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := by
  rw [← map_intCast (algebraMap ℚ_[l] ℂ_[l]), norm_algebraMap']
variable {l}
variable (l)
end ReciprocityTheory.ChartRestriction.L1
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (n : ℤ) : ‖(n : ℂ_[l])‖ ≤ 1 := by
  rw [kq_intnorm_lemma]
  first
  | exact padicNormE.norm_int_le_one n
  | exact Padic.norm_int_le_one n
end ReciprocityTheory.ChartRestriction.L1
