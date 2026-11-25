-- Prove2me | solution 1 for PI.KLW.NO.dvd_pow_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:02:59.28123+00:00
-- url     : https://prove2.me/submissions/8388a7ed-231d-42e2-85d7-cf70cc51aa26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Theorems.Thm_PI_KLW_NO_c_mem_O
import Theorems.Thm_PI_KLW_NO_natCast_mem_O
import Theorems.Thm_PI_KLW_NO_fixed_int
import Theorems.Thm_PI_KLW_NO_coprime_ne_zero

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
theorem _root_.solution (c : K →+* K) (hc : ∀ x, c (c x) = x) (hK : Module.finrank ℚ K = 2)
    (hne : ∃ z, c z ≠ z) (hp : p.Prime) {z : K} (hz : Rp K p z) (h0 : z ≠ 0) :
    ∃ J : ℕ, Rp K p ((p : K) ^ J / z) := by
  obtain ⟨s, hs, hsz⟩ := hz
  have hs0 : (s : K) ≠ 0 := by exact_mod_cast coprime_ne_zero hp hs
  set Y := (s : K) * z with hY
  have hY0 : Y ≠ 0 := mul_ne_zero hs0 h0
  have hcY0 : c Y ≠ 0 := by
    intro h; apply hY0; rw [← hc Y, h, map_zero]
  have hfix : c (Y * c Y) = Y * c Y := by rw [map_mul, hc, mul_comm]
  obtain ⟨m, hm⟩ := fixed_int c hK hne hfix (Subring.mul_mem _ hsz (c_mem_O c hsz))
  have hm0 : m ≠ 0 := by
    rintro rfl; apply mul_ne_zero hY0 hcY0; rw [hm]; simp
  obtain ⟨J, n', hn', hJ⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hm0) p hp.ne_one
  refine ⟨J, n', ((Nat.Prime.coprime_iff_not_dvd hp).2 hn').symm, ?_⟩
  have hnK : (m.natAbs : K) = (p : K) ^ J * n' := by exact_mod_cast hJ
  rcases Int.natAbs_eq m with h | h
  · have e : (m : K) = (m.natAbs : K) := by rw [← Int.cast_natCast]; exact congrArg _ h
    have e1 : Y * c Y = (p : K) ^ J * n' := by rw [hm, e, hnK]
    have : (n' : K) * ((p : K) ^ J / z) = (s : K) * c Y := by
      rw [← mul_div_assoc, div_eq_iff h0]
      rw [hY] at e1 ⊢
      linear_combination -e1
    rw [this]; exact Subring.mul_mem _ (natCast_mem_O s) (c_mem_O c hsz)
  · have e : (m : K) = -(m.natAbs : K) := by rw [← Int.cast_natCast, ← Int.cast_neg]; exact congrArg _ h
    have e1 : Y * c Y = -((p : K) ^ J * n') := by rw [hm, e, hnK]
    have : (n' : K) * ((p : K) ^ J / z) = -((s : K) * c Y) := by
      rw [← mul_div_assoc, div_eq_iff h0]
      rw [hY] at e1 ⊢
      linear_combination e1
    rw [this]; exact Subring.neg_mem _ (Subring.mul_mem _ (natCast_mem_O s) (c_mem_O c hsz))
end PI.KLW.NO
