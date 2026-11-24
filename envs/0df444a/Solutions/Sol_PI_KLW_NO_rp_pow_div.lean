-- Prove2me | solution 1 for PI.KLW.NO.rp_pow_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:57:10.170357+00:00
-- url     : https://prove2.me/submissions/d9f91bf1-d6e0-4024-9759-ee0c3a3963d7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Theorems.Thm_PI_KLW_NO_natCast_mem_O

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.NO
variable {K : Type} [Field K] [NumberField K] {p : ℕ}
namespace PI.KLW.NO
theorem _root_.solution (hp : p.Prime) {Q : ℕ} (hQ : Q ≠ 0) {k : ℕ} (hk : Q ≤ k) :
    Rp K p ((p : K) ^ k / Q) := by
  obtain ⟨e, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hQ p hp.ne_one
  have hn0 : n' ≠ 0 := by rintro rfl; simp at hQ
  have hek : e < k := by
    have h1 : p ^ e ≤ p ^ e * n' := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hn0)
    have h2 : k < p ^ k := Nat.lt_pow_self hp.one_lt
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 (by omega)
  refine ⟨n', ((Nat.Prime.coprime_iff_not_dvd hp).2 hn').symm, ?_⟩
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hn0K : (n' : K) ≠ 0 := by exact_mod_cast hn0
  have : (n' : K) * ((p : K) ^ k / ((p ^ e * n' : ℕ) : K)) = (p : K) ^ (k - e) := by
    push_cast
    rw [← Nat.sub_add_cancel hek.le, pow_add]
    field_simp
    simp
  rw [this]; exact Subring.pow_mem _ (natCast_mem_O p) _
end PI.KLW.NO
