-- Prove2me | solution 1 for PI.CompAtExist.muV_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:51.16798+00:00
-- url     : https://prove2.me/submissions/a557c349-7d27-49f1-b346-9b78a5d79c03

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_UniROfUniRT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionExistence_LeOneIffOfMulEqOne
import Theorems.Thm_PI_CompAtExist_muV_int_le_one
import Theorems.Thm_PI_CompAtExist_muV_int_lt_one_iff
import Theorems.Thm_PI_CompAtExist_muV_int_eq_one_iff
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
namespace PI.CompAtExist
open NumberField IsDedekindDomain ReciprocityTheory.Aut
section
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
private theorem exists_ringOfIntegers_not_mem_mul_eq_of_valuation_le (s : SplitPlace L) (x : L) (hx : s.w.valuation L x ≤ 1) :
    ∃ c t : 𝓞 L, c ∉ s.w.asIdeal ∧ algebraMap (𝓞 L) L c * x = algebraMap (𝓞 L) L t := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbL : algebraMap (𝓞 L) L b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).2 hb0
  have hvb : s.w.intValuation b ≠ 0 := s.w.intValuation_ne_zero b hb0
  rw [map_div₀, s.w.valuation_of_algebraMap, s.w.valuation_of_algebraMap] at hx
  have hab : s.w.intValuation a ≤ s.w.intValuation b := (div_le_one₀ (zero_lt_iff.2 hvb)).1 hx
  have hk0 : WithZero.log (s.w.intValuation b) ≤ 0 := by
    have := (WithZero.log_le_log hvb one_ne_zero).2 (s.w.intValuation_le_one b)
    rwa [WithZero.log_one] at this
  have hbe : s.w.intValuation b = WithZero.exp (-(((-WithZero.log (s.w.intValuation b)).toNat : ℕ) : ℤ)) := by
    rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hvb]
  set e : ℕ := (-WithZero.log (s.w.intValuation b)).toNat with he
  have ha_mem : a ∈ s.w.asIdeal ^ e := (s.w.intValuation_le_pow_iff_mem a e).1 (hab.trans hbe.le)
  have hb_mem : b ∈ s.w.asIdeal ^ e := (s.w.intValuation_le_pow_iff_mem b e).1 hbe.le
  have hb_not : b ∉ s.w.asIdeal ^ (e + 1) := by
    rw [← s.w.intValuation_le_pow_iff_mem, hbe, WithZero.exp_le_exp]
    push_cast
    omega
  obtain ⟨J, hJ⟩ : s.w.asIdeal ^ e ∣ Ideal.span {b} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hb_mem)
  have hJw : ¬ J ≤ s.w.asIdeal := by
    intro hle
    apply hb_not
    have : Ideal.span {b} ≤ s.w.asIdeal ^ (e + 1) := by
      rw [hJ, pow_succ]
      exact Ideal.mul_mono_right hle
    exact (Ideal.span_singleton_le_iff_mem _).1 this
  obtain ⟨c, hcJ, hcw⟩ := SetLike.not_le_iff_exists.1 hJw
  have hca : a * c ∈ Ideal.span {b} := by
    rw [hJ]
    exact Ideal.mul_mem_mul ha_mem hcJ
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hca
  refine ⟨c, t, hcw, ?_⟩
  rw [mul_div_assoc', div_eq_iff hbL, ← map_mul, ← map_mul, ht, mul_comm]
end
end PI.CompAtExist
end
end

set_option autoImplicit false
noncomputable section
open PI PI.CompAtExist
open NumberField IsDedekindDomain ReciprocityTheory.Aut
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
namespace PI.CompAtExist
theorem _root_.solution (s : SplitPlace L) (x : L) : muV s x ≤ 1 ↔ s.w.valuation L x ≤ 1 := by
  have hμint : ∀ r : 𝓞 L, r ∉ s.w.asIdeal → muV s (algebraMap (𝓞 L) L r) = 1 :=
    fun r hr => (muV_int_eq_one_iff s r).2 hr
  have hνint : ∀ r : 𝓞 L, r ∉ s.w.asIdeal → s.w.valuation L (algebraMap (𝓞 L) L r) = 1 := by
    intro r hr
    rw [s.w.valuation_of_algebraMap]
    exact le_antisymm (s.w.intValuation_le_one r)
      (not_lt.1 fun h => hr ((s.w.intValuation_lt_one_iff_mem r).1 h))
  constructor
  · intro hμ
    by_contra hν
    push_neg at hν
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hν
    have hν' : s.w.valuation L x⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ hν.le
    obtain ⟨c, t, hc, ht⟩ := exists_ringOfIntegers_not_mem_mul_eq_of_valuation_le s x⁻¹ hν'
    have hνt : s.w.valuation L (algebraMap (𝓞 L) L t) < 1 := by
      rw [← ht, map_mul, hνint c hc, one_mul, map_inv₀]
      exact inv_lt_one_of_one_lt₀ hν
    have htw : t ∈ s.w.asIdeal := by
      rw [s.w.valuation_of_algebraMap] at hνt
      exact (s.w.intValuation_lt_one_iff_mem t).1 hνt
    have hμt : muV s (algebraMap (𝓞 L) L t) < 1 := (muV_int_lt_one_iff s t).2 htw
    rw [← ht, map_mul, hμint c hc, one_mul, map_inv₀] at hμt
    have hμx0 : muV s x ≠ 0 := (muV s).ne_zero_iff.2 hx0
    have h1 := (inv_lt_one₀ (zero_lt_iff.2 hμx0)).1 hμt
    exact absurd hμ (not_le.2 h1)
  · intro hν
    obtain ⟨c, t, hc, ht⟩ := exists_ringOfIntegers_not_mem_mul_eq_of_valuation_le s x hν
    have h1 := muV_int_le_one s t
    rw [← ht, map_mul, hμint c hc, one_mul] at h1
    exact h1
end PI.CompAtExist
