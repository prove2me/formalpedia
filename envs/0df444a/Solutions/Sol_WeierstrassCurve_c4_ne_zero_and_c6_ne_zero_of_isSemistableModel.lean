-- Prove2me | solution 1 for WeierstrassCurve.c4_ne_zero_and_c6_ne_zero_of_isSemistableModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/4801c85c-c9e7-5f0f-84c3-2d7d8e10e718

import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_WeierstrassCurve_Delta_ne_one_and_Delta_ne_neg_one
import Mathlib.Data.Nat.Prime.Int
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_c4_ne_zero_and_c6_ne_zero_of_isSemistableModel

namespace M4cP4E2

theorem false_of_forall_prime_not_dvd (W : WeierstrassCurve ℤ)
    (hno : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ W.Δ) : False := by
  have h1 : W.Δ.natAbs = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    exact hno p hp (Int.ofNat_dvd_left.mpr hpd)
  rcases Int.natAbs_eq_iff.mp h1 with h | h
  · exact (WeierstrassCurve.Delta_ne_one_and_Delta_ne_neg_one W).1 (by simpa using h)
  · exact (WeierstrassCurve.Delta_ne_one_and_Delta_ne_neg_one W).2 (by simpa using h)

theorem main (W : WeierstrassCurve ℤ) (hW : W.IsSemistableModel) : W.c₄ ≠ 0 ∧ W.c₆ ≠ 0 := by
  refine ⟨fun hc4 => ?_, fun hc6 => ?_⟩
  ·
    exact false_of_forall_prime_not_dvd W fun p hp hpΔ => hW p hp hpΔ (hc4 ▸ dvd_zero _)
  ·
    refine false_of_forall_prime_not_dvd W fun p hp hpΔ => hW p hp hpΔ ?_
    have hrel := W.c_relation
    rw [hc6, zero_pow two_ne_zero, sub_zero] at hrel
    have h3 : (p : ℤ) ∣ W.c₄ ^ 3 := hrel ▸ dvd_mul_of_dvd_right hpΔ 1728
    exact (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow h3

end M4cP4E2

theorem solution (W : WeierstrassCurve ℤ) (hW : W.IsSemistableModel) : W.c₄ ≠ 0 ∧ W.c₆ ≠ 0 :=
  M4cP4E2.main W hW

end S_WeierstrassCurve_c4_ne_zero_and_c6_ne_zero_of_isSemistableModel
end P2MW
export P2MW.S_WeierstrassCurve_c4_ne_zero_and_c6_ne_zero_of_isSemistableModel (solution)
