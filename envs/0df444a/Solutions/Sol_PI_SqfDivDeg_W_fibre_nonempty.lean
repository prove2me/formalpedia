-- Prove2me | solution 1 for PI.SqfDivDeg.W.fibre_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:22:51.524692+00:00
-- url     : https://prove2.me/submissions/0cc95e0b-94dd-4d8c-806b-5e3b56ec5c6e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_FibreNonempty
import Theorems.Thm_PI_SqfDivDeg_W_mem_Mon


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open PI PI.SqfDivDeg PI.SqfDivDeg.W
namespace PI.SqfDivDeg.W
theorem _root_.solution {g r a : ℕ} [Fact g.Prime] (har : a ≤ r) {f : (ZMod g)[X]}
    (hf : PI.SqfLab.Eiv g r a f) :
    ∃ q h, q ∈ Mon g a ∧ h ∈ Mon g (r - a) ∧ q * h = f := by
  obtain ⟨⟨hmon, hdeg, -⟩, -, q, hqf, hqa⟩ := hf
  have hf0 : f ≠ 0 := hmon.ne_zero
  have hq0 : q ≠ 0 := by rintro rfl; exact hf0 (zero_dvd_iff.mp hqf)
  obtain ⟨k, hk⟩ := hqf
  have hl : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq0
  have m1 : (q * C (q.leadingCoeff)⁻¹).Monic := monic_mul_leadingCoeff_inv hq0
  have d1 : (q * C (q.leadingCoeff)⁻¹).natDegree = a := by
    rw [natDegree_mul_C (inv_ne_zero hl), hqa]
  have e : (q * C (q.leadingCoeff)⁻¹) * (C q.leadingCoeff * k) = f := by
    rw [hk]
    calc q * C (q.leadingCoeff)⁻¹ * (C q.leadingCoeff * k)
        = q * (C ((q.leadingCoeff)⁻¹ * q.leadingCoeff)) * k := by rw [C_mul]; ring
      _ = q * k := by rw [inv_mul_cancel₀ hl, C_1, mul_one]
  have m2 : (C q.leadingCoeff * k).Monic := m1.of_mul_monic_left (by rw [e]; exact hmon)
  have d2 : (C q.leadingCoeff * k).natDegree = r - a := by
    have := m1.natDegree_mul m2
    rw [e, hdeg, d1] at this
    omega
  exact ⟨_, _, mem_Mon.mpr ⟨m1, d1⟩, mem_Mon.mpr ⟨m2, d2⟩, e⟩
end PI.SqfDivDeg.W
