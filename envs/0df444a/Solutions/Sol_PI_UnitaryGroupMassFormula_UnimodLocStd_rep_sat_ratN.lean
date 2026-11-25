-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_sat_ratN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:51:15.69338+00:00
-- url     : https://prove2.me/submissions/e8478bb4-6d46-4860-bca3-f7b2f6782114

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
theorem _root_.solution (hl : l.Prime) {v : m → ℂ} (hv : SatMem l Λ v) (r : ℤ) (k : ℕ) (hk : ¬ l ∣ k) :
    SatMem l Λ (((r : ℂ) / k) • v) := by
  obtain ⟨n, hn, hnv⟩ := hv
  have hk0 : (k : ℂ) ≠ 0 := by
    rintro h; exact hk (by rw [Nat.cast_eq_zero.mp h]; exact dvd_zero _)
  refine ⟨n * k, fun h => (hl.dvd_mul.mp h).elim hn hk, ?_⟩
  have e : (n * k) • (((r : ℂ) / k) • v) = r • (n • v) := by
    funext i; simp only [Pi.smul_apply, nsmul_eq_mul, zsmul_eq_mul, smul_eq_mul, Nat.cast_mul, Pi.mul_apply, Pi.natCast_apply, Pi.intCast_apply]; field_simp
  rw [e]
  exact Λ.zsmul_mem hnv _
end PI.UnitaryGroupMassFormula.UnimodLocStd
