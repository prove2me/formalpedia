-- Prove2me | solution 1 for PI.ArtSch.WittLiftWork.lim_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:59:36.565847+00:00
-- url     : https://prove2.me/submissions/42ec3106-f2a0-4794-b84c-3c0d5be18195

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittCoefficients_CoeffEqOfSubMem
import Theorems.Thm_PI_ArtSch_WittLiftWork_coeff_eq_of_sub_mem
import Theorems.Thm_P2M_PI_ArtSch_WittLiftWork___mem_05e7988b8311
import Theorems.Thm_PI_ArtSch_WittLiftWork_lim_sub

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
theorem _root_.solution (x : WittVector p k) : δ (lim hAS x) = x := by
  have key : ∀ n, x - δ (lim hAS x) ∈ I n := by
    intro n
    have h1 := (seq hAS x n).2
    have h2 := δ_mem (lim_sub hAS x n)
    have h3 := δ_add (seq hAS x n).1 (lim hAS x - (seq hAS x n).1)
    rw [show (seq hAS x n).1 + (lim hAS x - (seq hAS x n).1) = lim hAS x from by abel] at h3
    have e : x - δ (lim hAS x) =
        (x - δ (seq hAS x n).1) - δ (lim hAS x - (seq hAS x n).1) := by
      rw [h3]; abel
    rw [e]
    exact Ideal.sub_mem _ h1 h2
  refine WittVector.ext fun i => ?_
  exact (coeff_eq_of_sub_mem (key (i + 1)) (Nat.lt_succ_self i)).symm
end PI.ArtSch.WittLiftWork
