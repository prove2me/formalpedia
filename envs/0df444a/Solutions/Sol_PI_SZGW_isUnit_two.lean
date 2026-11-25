-- Prove2me | solution 1 for PI.SZGW.isUnit_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:17:39.126147+00:00
-- url     : https://prove2.me/submissions/490b37e6-e754-4040-b45d-a7b535b6387e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitZeroClosedness_ZcFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitZeroClosedness_IsClosedSimeqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.SZGW
open PI.BeDiagZp.ContPf
namespace PI.SZGW
theorem _root_.solution {p : ℕ} [hp : Fact p.Prime] (h2 : p ≠ 2) : IsUnit (2 : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) ?_
  by_contra hlt
  rw [not_le] at hlt
  have e : (2 : ℤ_[p]) = ((2 : ℤ) : ℤ_[p]) := by norm_cast
  rw [e, PadicInt.norm_int_lt_one_iff_dvd] at hlt
  have hd : p ∣ 2 := by exact_mod_cast hlt
  have hle := Nat.le_of_dvd (by norm_num) hd
  have hge := hp.out.two_le
  omega
end PI.SZGW
