-- Prove2me | solution 1 for UpperTheory.Ram.Fun.sum_delta_log_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:59:35.054555+00:00
-- url     : https://prove2.me/submissions/175558df-888c-460d-90c3-af52db51dc0e

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
theorem _root_.solution (E : Type) [Field E] [NumberField E] (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) :
    ∑ l ∈ S, (padicValInt l (discr E) : ℝ) / (Module.finrank ℚ E : ℝ) * Real.log l ≤
      Real.log (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) := by
  have hd : discr E ≠ 0 := discr_ne_zero E
  have hpos : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.2 (by exact_mod_cast hd)
  have hn : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  rw [Real.log_rpow hpos]
  have e : (((discr E).natAbs : ℕ) : ℝ) = |(discr E : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have h := sum_padicValNat_log_le (Int.natAbs_ne_zero.2 hd) S hS
  rw [e] at h
  calc ∑ l ∈ S, (padicValInt l (discr E) : ℝ) / (Module.finrank ℚ E : ℝ) * Real.log l
      = (∑ l ∈ S, (padicValNat l (discr E).natAbs : ℝ) * Real.log l) / (Module.finrank ℚ E : ℝ) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun l _ => by
          rw [show padicValInt l (discr E) = padicValNat l (discr E).natAbs from rfl]; ring
    _ ≤ Real.log |(discr E : ℝ)| / (Module.finrank ℚ E : ℝ) := div_le_div_of_nonneg_right h hn.le
    _ = _ := by ring
end UpperTheory.Ram.Fun
