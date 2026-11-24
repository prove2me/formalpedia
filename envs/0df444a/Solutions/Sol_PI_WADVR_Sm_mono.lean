-- Prove2me | solution 1 for PI.WADVR.Sm.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:24.736302+00:00
-- url     : https://prove2.me/submissions/1b089320-0a8e-4662-9ec0-93413be4aafe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit
import Theorems.Thm_PI_WADVR_alg_ne_zero

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
namespace Sm
theorem _root_.solution (hϖ : Irreducible ϖ) {k l : ℤ} {a : Q} (ha : Sm Q ϖ k a) (h : l ≤ k) :
    Sm Q ϖ l a := by
  obtain ⟨c, rfl⟩ := ha
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h)
  refine ⟨ϖ ^ n * c, ?_⟩
  have : k = l + (n : ℤ) := by omega
  rw [this, zpow_add₀ (alg_ne_zero hϖ), zpow_natCast, map_mul, map_pow]
  ring
end Sm
end PI.WADVR
