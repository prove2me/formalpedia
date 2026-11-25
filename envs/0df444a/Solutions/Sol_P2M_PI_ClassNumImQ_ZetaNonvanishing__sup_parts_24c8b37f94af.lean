-- Prove2me | solution 1 for P2M_PI_ClassNumImQ_ZetaNonvanishing__sup_parts_24c8b37f94af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:55:24.675578+00:00
-- url     : https://prove2.me/submissions/aed86b71-2fc4-4954-ab69-fb623817c2bd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_SpanNatCastSupEqTop
import Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__sup_mul_sup_eq_ed49e89e31f7
import Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__span_natCast_sup_eq_top_26fc201e2cd4
import Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__span_le_of_absNorm_fd6c4dee4894

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.ClassNumImQ PI.ClassNumImQ.ZetaNonvanishing₂
variable {K : Type} [Field K] [NumberField K]
namespace PI.ClassNumImQ.ZetaNonvanishing₂
theorem _root_.solution {m n : ℕ} (hmn : m.Coprime n) (hm : 0 < m) (hn : 0 < n) {A : Ideal (𝓞 K)}
    (hA : Ideal.absNorm A = m * n) :
    (A ⊔ Ideal.span {(m : 𝓞 K)}) * (A ⊔ Ideal.span {(n : 𝓞 K)}) = A ∧
      Ideal.absNorm (A ⊔ Ideal.span {(m : 𝓞 K)}) = m ∧
      Ideal.absNorm (A ⊔ Ideal.span {(n : 𝓞 K)}) = n := by
  have hprod : (A ⊔ Ideal.span {(m : 𝓞 K)}) * (A ⊔ Ideal.span {(n : 𝓞 K)}) = A := by
    refine sup_mul_sup_eq A _ _ (span_natCast_sup_eq_top hmn) ?_
    rw [Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul]
    exact span_le_of_absNorm hA
  have hN := congrArg Ideal.absNorm hprod
  rw [map_mul, hA] at hN
  set a := Ideal.absNorm (A ⊔ Ideal.span {(m : 𝓞 K)})
  set c := Ideal.absNorm (A ⊔ Ideal.span {(n : 𝓞 K)})
  have ha : a ∣ m ^ Module.finrank ℤ (𝓞 K) := by
    rw [← Ideal.absNorm_span_natCast]
    exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
  have hc : c ∣ n ^ Module.finrank ℤ (𝓞 K) := by
    rw [← Ideal.absNorm_span_natCast]
    exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
  have ha' : a ∣ m := by
    have hcop : a.Coprime n := Nat.Coprime.coprime_dvd_left ha (Nat.Coprime.pow_left _ hmn)
    exact hcop.dvd_of_dvd_mul_right ⟨c, hN.symm⟩
  have hc' : c ∣ n := by
    have hcop : c.Coprime m := Nat.Coprime.coprime_dvd_left hc (Nat.Coprime.pow_left _ hmn.symm)
    exact hcop.dvd_of_dvd_mul_left ⟨a, by rw [← hN]; ring⟩
  have ha1 : a ≤ m := Nat.le_of_dvd hm ha'
  have hc1 : c ≤ n := Nat.le_of_dvd hn hc'
  have hae : a = m := by
    by_contra hne
    have hlt : a < m := lt_of_le_of_ne ha1 hne
    have : a * c < m * n := by
      calc a * c ≤ a * n := Nat.mul_le_mul_left _ hc1
        _ < m * n := Nat.mul_lt_mul_of_pos_right hlt hn
    omega
  have hce : c = n := by
    rw [hae] at hN
    exact Nat.eq_of_mul_eq_mul_left hm hN
  exact ⟨hprod, hae, hce⟩
end PI.ClassNumImQ.ZetaNonvanishing₂
