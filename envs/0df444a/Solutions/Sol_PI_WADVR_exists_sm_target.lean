-- Prove2me | solution 1 for PI.WADVR.exists_sm_target
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:05:54.270699+00:00
-- url     : https://prove2.me/submissions/8ea729c4-c2ec-4598-b822-cf09c86f139b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WADVR
variable {W Q : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q]
  [Algebra W Q] [IsFractionRing W Q]
variable {ϖ : W}
namespace PI.WADVR
theorem _root_.solution (hϖ : Irreducible ϖ) {p : ℕ} (hp : (p : Q) ≠ 0) (N : ℕ) :
    ∃ n : ℕ, ∀ q : Q, Sm Q ϖ n q → ∃ c : W, q = (p : Q) ^ N * algebraMap W Q c := by
  have hpW : ((p : W) ^ N) ≠ 0 := by
    refine pow_ne_zero _ ?_
    intro h
    apply hp
    rw [← map_natCast (algebraMap W Q), h, map_zero]
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hpW hϖ
  refine ⟨n, fun q ⟨c, hc⟩ => ⟨(u : W) * c, ?_⟩⟩
  rw [hc, zpow_natCast, ← map_pow, ← hu, ← map_natCast (algebraMap W Q), ← map_pow, ← map_mul,
    ← map_mul, mul_assoc]
end PI.WADVR
