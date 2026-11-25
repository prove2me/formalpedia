-- Prove2me | solution 1 for PI.VolStabSW.exists_appr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:55:40.546443+00:00
-- url     : https://prove2.me/submissions/510e9ea0-c14c-4ea4-b6c8-2310bcbee9a4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensCntRes
import Theorems.Thm_PI_VolStabSW_vcoe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.VolStabSW
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
section Res
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
private theorem appr_unit_lemma (m c : 𝓞 F) (hc : c ∉ v.asIdeal) :
    ∃ a : 𝓞 F, v.valuation F (algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F c -
      algebraMap (𝓞 F) F a) < 1 := by
  obtain ⟨c', hc'⟩ : ∃ c' : 𝓞 F, c * c' - 1 ∈ v.asIdeal := by
    haveI : v.asIdeal.IsMaximal := v.isMaximal
    letI := Ideal.Quotient.field v.asIdeal
    have hne : Ideal.Quotient.mk v.asIdeal c ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨c', hc'⟩ := Ideal.Quotient.mk_surjective (I := v.asIdeal) (Ideal.Quotient.mk v.asIdeal c)⁻¹
    refine ⟨c', ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc', mul_inv_cancel₀ hne, map_one, sub_self]
  refine ⟨m * c', ?_⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc v.asIdeal.zero_mem
  have hcF : algebraMap (𝓞 F) F c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hc0
  have hvc : v.valuation F (algebraMap (𝓞 F) F c) = 1 :=
    le_antisymm (v.valuation_le_one c) (not_lt.mp fun h => hc ((v.valuation_lt_one_iff_mem c).mp h))
  have heq : algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F c - algebraMap (𝓞 F) F (m * c') =
      algebraMap (𝓞 F) F m * algebraMap (𝓞 F) F (1 - c * c') / algebraMap (𝓞 F) F c := by
    rw [map_mul, map_sub, map_one, map_mul]
    first
      | (field_simp; ring)
      | field_simp
  have h1 : v.valuation F (algebraMap (𝓞 F) F (1 - c * c')) < 1 := by
    rw [v.valuation_lt_one_iff_mem]
    have h2 : 1 - c * c' = -(c * c' - 1) := by ring
    rw [h2]
    exact v.asIdeal.neg_mem hc'
  have hm1 := v.valuation_le_one (K := F) m
  rw [heq, map_div₀, hvc, div_one, map_mul]
  calc v.valuation F (algebraMap (𝓞 F) F m) * v.valuation F (algebraMap (𝓞 F) F (1 - c * c'))
      ≤ 1 * v.valuation F (algebraMap (𝓞 F) F (1 - c * c')) := by gcongr
    _ < 1 := by rw [one_mul]; exact h1
private theorem appr_den_lemma_2 (k : F) (hk : v.valuation F k ≤ 1) :
    ∃ m c : 𝓞 F, c ∉ v.asIdeal ∧ k = algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F c := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) k
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdF : algebraMap (𝓞 F) F d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  have hB : ∀ r : 𝓞 F, v.valuation F (algebraMap (𝓞 F) F r) = v.intValuation r := by
    intro r
    first
      | exact HeightOneSpectrum.valuation_of_algebraMap v r
      | exact v.valuation_of_algebraMap r
      | simp
  have hιd0 : v.intValuation d ≠ 0 := by
    rw [← hB]
    exact (Valuation.ne_zero_iff _).mpr hdF
  have hιd1 : v.intValuation d ≤ 1 := by
    rw [← hB]
    exact v.valuation_le_one d
  have hLe : WithZero.exp (WithZero.log (v.intValuation d)) = v.intValuation d := WithZero.exp_log hιd0
  have hL0 : WithZero.log (v.intValuation d) ≤ 0 := by
    have h := hιd1
    rw [← hLe, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    exact h
  obtain ⟨e, he⟩ : ∃ e : ℕ, (e : ℤ) = -WithZero.log (v.intValuation d) :=
    ⟨(-WithZero.log (v.intValuation d)).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hιd : v.intValuation d = WithZero.exp (-(e : ℤ)) := by
    rw [he, neg_neg, hLe]
  have hdiv : v.asIdeal ^ e ∣ Ideal.span {d} :=
    (HeightOneSpectrum.intValuation_le_pow_iff_dvd v d e).mp (le_of_eq hιd)
  have hndiv : ¬ v.asIdeal ^ (e + 1) ∣ Ideal.span {d} := by
    intro h
    have h2 := (HeightOneSpectrum.intValuation_le_pow_iff_dvd v d (e + 1)).mpr h
    rw [hιd, WithZero.exp_le_exp] at h2
    push_cast at h2
    omega
  obtain ⟨J, hJ⟩ := hdiv
  have hJP : ¬ J ≤ v.asIdeal := by
    intro h
    apply hndiv
    rw [hJ, pow_succ]
    exact mul_dvd_mul_left _ (Ideal.dvd_iff_le.mpr h)
  obtain ⟨c, hcJ, hcP⟩ := SetLike.not_le_iff_exists.mp hJP
  have hn : n ∈ v.asIdeal ^ e := by
    have hιn : v.intValuation n ≤ v.intValuation d := by
      have h := hk
      rw [map_div₀, hB, hB] at h
      calc v.intValuation n = v.intValuation n / v.intValuation d * v.intValuation d := by
            rw [div_mul_cancel₀ _ hιd0]
        _ ≤ 1 * v.intValuation d := by gcongr
        _ = v.intValuation d := one_mul _
    rw [hιd] at hιn
    exact Ideal.dvd_span_singleton.mp ((HeightOneSpectrum.intValuation_le_pow_iff_dvd v n e).mp hιn)
  have hcn : c * n ∈ Ideal.span {d} := by
    rw [hJ, mul_comm c n]
    exact Ideal.mul_mem_mul hn hcJ
  obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.mp hcn
  refine ⟨m, c, hcP, ?_⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hcP v.asIdeal.zero_mem
  have hcF : algebraMap (𝓞 F) F c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hc0
  rw [div_eq_div_iff hdF hcF, ← map_mul, ← map_mul, mul_comm n c, ← hm]
end Res
section Count
end Count
end PI.VolStabSW
end
end

set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabSW
theorem _root_.solution {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ a : 𝓞 F, Valued.v (x - iO v a) < 1 := by
  have hx1 : Valued.v x ≤ 1 := hx
  have hnhds : {y : Fv F v | Valued.v (y - x) < 1} ∈ 𝓝 x :=
    Valued.mem_nhds.mpr ⟨1, fun y hy => by simpa using hy⟩
  obtain ⟨_, hy, k, rfl⟩ :=
    mem_closure_iff_nhds.mp (HeightOneSpectrum.denseRange_algebraMap F v x) _ hnhds
  have hy' : Valued.v (x - algebraMap F (Fv F v) k) < 1 := by
    have h := hy
    rwa [Set.mem_setOf_eq, ← neg_sub, Valuation.map_neg] at h
  have hk1 : Valued.v (algebraMap F (Fv F v) k) ≤ 1 := by
    have h := Valuation.map_add_le Valued.v (le_of_lt hy) hx1
    rwa [sub_add_cancel] at h
  rw [vcoe] at hk1
  obtain ⟨m, c, hc, rfl⟩ := appr_den_lemma_2 v k hk1
  obtain ⟨a, ha⟩ := appr_unit_lemma v m c hc
  refine ⟨a, ?_⟩
  have h2 : Valued.v (algebraMap F (Fv F v) (algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F c) - iO v a) < 1 := by
    show Valued.v (algebraMap F (Fv F v) _ - algebraMap F (Fv F v) (algebraMap (𝓞 F) F a)) < 1
    rw [← map_sub, vcoe]
    exact ha
  have h3 : x - iO v a = (x - algebraMap F (Fv F v) (algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F c)) +
      (algebraMap F (Fv F v) (algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F c) - iO v a) := by
    ring
  rw [h3]
  exact Valuation.map_add_lt Valued.v hy' h2
end PI.VolStabSW
