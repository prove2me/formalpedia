-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_NormLeOneOfMonicRoot_norm_le_one_of_monic_root__86b9da74710a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:14:26.803386+00:00
-- url     : https://prove2.me/submissions/399aeae1-54c2-40db-8b11-afc6009cee26

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormLeOneOfMonicRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.NormLeOneOfMonicRoot
theorem _root_.solution.{u_1, u_2} :
    ∀ {R : Type u_1} {L : Type u_2} [inst : CommRing R] [inst_1 : NormedField L] [IsUltrametricDist L]
    (φ : R →+* L),
    (∀ (a : R), ‖(φ : R → L) a‖ ≤ (1 : ℝ)) →
      ∀ (x : L) (p : Polynomial R), p.Monic → Polynomial.eval₂ φ x p = (0 : L) → ‖x‖ ≤ (1 : ℝ) := by
  intro R L _ _ _ φ hφ x p hp hx
  by_contra hlt
  have h1 : 1 < ‖x‖ := not_le.mp hlt
  have h0 : 0 < ‖x‖ := lt_trans one_pos h1
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one,
    one_mul] at hx
  have hx' : x ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, φ (p.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_right hx
  have hb : ‖∑ i ∈ Finset.range p.natDegree, φ (p.coeff i) * x ^ i‖
      ≤ ‖x‖ ^ p.natDegree / ‖x‖ := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    have hi' : i + 1 ≤ p.natDegree := Finset.mem_range.mp hi
    rw [norm_mul, norm_pow, le_div_iff₀ h0]
    calc ‖φ (p.coeff i)‖ * ‖x‖ ^ i * ‖x‖ ≤ 1 * ‖x‖ ^ i * ‖x‖ := by
          gcongr
          exact hφ _
      _ = ‖x‖ ^ (i + 1) := by ring
      _ ≤ ‖x‖ ^ p.natDegree := pow_le_pow_right₀ h1.le hi'
  rw [← norm_neg, ← hx', norm_pow] at hb
  have hlt' : ‖x‖ ^ p.natDegree / ‖x‖ < ‖x‖ ^ p.natDegree :=
    div_lt_self (by positivity) h1
  exact absurd hb (not_le.mpr hlt')
end UpperTheory.Reformulated.B.NormLeOneOfMonicRoot
