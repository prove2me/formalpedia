-- Prove2me | solution 1 for PI.ArtSch.WittLiftWork.lim_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:52:42.14616+00:00
-- url     : https://prove2.me/submissions/db1ae44a-ad26-4ec2-97b4-acde3eac0e09

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittCoefficients_CoeffEqOfSubMem
import Theorems.Thm_PI_ArtSch_WittLiftWork_coeff_eq_of_sub_mem
import Theorems.Thm_PI_ArtSch_WittLiftWork_sub_mem_of_coeff_eq
import Theorems.Thm_PI_ArtSch_WittLiftWork_seq_stable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ArtSch PI.ArtSch.WittLiftWork
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [CommRing k]
variable [CharP k p]
variable (hAS : ∀ a : k, ∃ y : k, y ^ p - y = a)
include hAS
namespace PI.ArtSch.WittLiftWork
theorem _root_.solution (x : WittVector p k) (n : ℕ) : lim hAS x - (seq hAS x n).1 ∈ I n := by
  refine sub_mem_of_coeff_eq fun i hi => ?_
  have h := seq_stable hAS x (i + 1) n (by omega)
  exact (coeff_eq_of_sub_mem h (Nat.lt_succ_self i)).symm
end PI.ArtSch.WittLiftWork
