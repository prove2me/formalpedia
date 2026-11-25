-- Prove2me | solution 1 for PI.ProdFormulaE.Frac.padicNorm_le_one_of_den_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:05:49.902516+00:00
-- url     : https://prove2.me/submissions/b9233436-e5f7-4c18-9966-39e10c12df6c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_DenEqOneOfForallPadicNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace PI.ProdFormulaE.Frac
private theorem padicNorm_le_one_iff_not_dvd_den {q : ℕ} [Fact q.Prime] (r : ℚ) :
    padicNorm q r ≤ 1 ↔ ¬ q ∣ r.den := by
  have hmul : padicNorm q r * padicNorm q (r.den : ℚ) = padicNorm q (r.num : ℚ) := by
    rw [← padicNorm.mul, Rat.mul_den_eq_num]
  constructor
  · intro h hd
    have h1 : padicNorm q (r.den : ℚ) < 1 := (padicNorm.nat_lt_one_iff _).2 hd
    have h2 : padicNorm q (r.num : ℚ) < 1 := by
      rw [← hmul]
      calc padicNorm q r * padicNorm q (r.den : ℚ) ≤ 1 * padicNorm q (r.den : ℚ) :=
            mul_le_mul_of_nonneg_right h (padicNorm.nonneg _)
        _ < 1 := by rw [one_mul]; exact h1
    have h4 : q ∣ r.num.natAbs := Int.natCast_dvd.1 ((padicNorm.int_lt_one_iff _).1 h2)
    have h5 := Nat.dvd_gcd h4 hd
    rw [r.reduced.gcd_eq_one] at h5
    exact (Nat.Prime.not_dvd_one Fact.out) h5
  · intro hd
    have h1 : padicNorm q (r.den : ℚ) = 1 := (padicNorm.nat_eq_one_iff _).2 hd
    rw [h1, mul_one] at hmul
    rw [hmul]
    exact padicNorm.of_int _
end PI.ProdFormulaE.Frac
end
end

set_option autoImplicit false
noncomputable section
open Finset
open PI PI.ProdFormulaE PI.ProdFormulaE.Frac
namespace PI.ProdFormulaE.Frac
theorem _root_.solution {q : ℕ} [Fact q.Prime] {a : ℚ} (ha : a.den = 1) :
    padicNorm q a ≤ 1 := by
  rw [padicNorm_le_one_iff_not_dvd_den, ha]
  exact Nat.Prime.not_dvd_one Fact.out
end PI.ProdFormulaE.Frac
