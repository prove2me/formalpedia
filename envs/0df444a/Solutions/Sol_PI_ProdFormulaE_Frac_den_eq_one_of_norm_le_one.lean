-- Prove2me | solution 1 for PI.ProdFormulaE.Frac.den_eq_one_of_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:03.99949+00:00
-- url     : https://prove2.me/submissions/9b358db4-76ad-4561-a001-16026db6f084

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
theorem _root_.solution {l : ℕ} [hl : Fact l.Prime] {a : ℚ} {n : ℕ}
    (ha : a.den = l ^ n) {T : ℚ_[l]} (hT : ‖T‖ ≤ 1) (hTa : ‖T - (a : ℚ_[l])‖ ≤ 1) :
    a.den = 1 := by
  have h1 : ‖(a : ℚ_[l])‖ ≤ 1 := by
    have e : (a : ℚ_[l]) = T + -(T - (a : ℚ_[l])) := by ring
    rw [e]
    refine le_trans (Padic.nonarchimedean _ _) (max_le hT ?_)
    rw [norm_neg]
    exact hTa
  have h2 : padicNorm l a ≤ 1 := by
    have e : ‖((a : ℚ) : ℚ_[l])‖ = _ := Padic.eq_padicNorm a
    have h' : ((padicNorm l a : ℚ) : ℝ) ≤ 1 := by
      rw [← e]
      exact h1
    exact_mod_cast h'
  have h3 := (padicNorm_le_one_iff_not_dvd_den a).1 h2
  rw [ha] at h3 ⊢
  rcases n with _ | n
  · simp
  · exact absurd (dvd_pow_self l (Nat.succ_ne_zero n)) h3
end PI.ProdFormulaE.Frac
