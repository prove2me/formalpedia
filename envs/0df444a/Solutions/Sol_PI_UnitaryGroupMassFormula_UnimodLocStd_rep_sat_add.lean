-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_sat_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:58:03.586654+00:00
-- url     : https://prove2.me/submissions/ce307add-3db2-4b78-b2d0-042e8478ea44

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {m : Type} (l : ℕ) (Λ : AddSubgroup (m → ℂ))
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (hl : l.Prime) {v w : m → ℂ} (hv : SatMem l Λ v) (hw : SatMem l Λ w) : SatMem l Λ (v + w) := by
  obtain ⟨n, hn, hnv⟩ := hv
  obtain ⟨k, hk, hkw⟩ := hw
  refine ⟨n * k, fun h => (hl.dvd_mul.mp h).elim hn hk, ?_⟩
  have e : (n * k) • (v + w) = k • (n • v) + n • (k • w) := by
    funext i; simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_mul, Pi.mul_apply, Pi.natCast_apply]; ring
  rw [e]
  exact Λ.add_mem (Λ.nsmul_mem hnv k) (Λ.nsmul_mem hkw n)
end PI.UnitaryGroupMassFormula.UnimodLocStd
