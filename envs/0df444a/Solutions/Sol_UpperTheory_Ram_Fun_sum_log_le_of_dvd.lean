-- Prove2me | solution 1 for UpperTheory.Ram.Fun.sum_log_le_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:04:15.999674+00:00
-- url     : https://prove2.me/submissions/ca1429af-b387-4e70-a4de-749df8068376

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsPrimeOfDifferentLe
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FunKit
import Theorems.Thm_UpperTheory_Ram_Fun_sum_padicValNat_log_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset
noncomputable section
open UpperTheory UpperTheory.Ram UpperTheory.Ram.Fun
namespace UpperTheory.Ram.Fun
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime ∧ l ∣ n) :
    ∑ l ∈ S, Real.log l ≤ Real.log n := by
  refine le_trans (Finset.sum_le_sum fun l hl => ?_) (sum_padicValNat_log_le hn S fun l hl => (hS l hl).1)
  haveI := Fact.mk (hS l hl).1
  have h1 : (1 : ℝ) ≤ padicValNat l n := by exact_mod_cast one_le_padicValNat_of_dvd hn (hS l hl).2
  have := Real.log_natCast_nonneg l
  nlinarith
end UpperTheory.Ram.Fun
