-- Prove2me | solution 1 for PI.CompDegEF.kerProp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:40:12.190624+00:00
-- url     : https://prove2.me/submissions/87b4ae31-5e99-48c6-8150-fd0812d3e559

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_NormLeOneOfInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_IsEquivAdicAbvNormAbv
import Theorems.Thm_PI_CompDegEF_normAbv_apply
import Theorems.Thm_PI_CompDegEF_intValuation_natCast
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
namespace PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc
private lemma frac_lemma' {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (u : E)
    (hu : v.valuation E u ≤ 1) :
    ∃ c j : 𝓞 E, j ∉ v.asIdeal ∧ u = algebraMap (𝓞 E) E c / algebraMap (𝓞 E) E j := by
  classical
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) u
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdE : algebraMap (𝓞 E) E d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d})).factors :=
    ⟨_, rfl⟩
  have hvd : v.intValuation d = WithZero.exp (-(k : ℤ)) := by
    rw [v.intValuation_if_neg hd0, hk]
  have hpos : 0 < v.intValuation d := by
    rw [hvd]; exact zero_lt_iff.mpr WithZero.exp_ne_zero
  rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    div_le_one₀ hpos, hvd] at hu
  have hdvda : v.asIdeal ^ k ∣ Ideal.span {a} := (v.intValuation_le_pow_iff_dvd a k).mp hu
  have hdvdd : v.asIdeal ^ k ∣ Ideal.span {d} := (v.intValuation_le_pow_iff_dvd d k).mp hvd.le
  obtain ⟨J, hJ⟩ := hdvdd
  have hJv : ¬ (J : Set (𝓞 E)) ⊆ v.asIdeal := by
    intro hle
    have h2 : v.asIdeal ^ (k + 1) ∣ Ideal.span {d} := by
      rw [hJ, pow_succ]
      exact mul_dvd_mul_left _ (Ideal.dvd_iff_le.mpr hle)
    have h3 := (v.intValuation_le_pow_iff_dvd d (k + 1)).mpr h2
    rw [hvd, WithZero.exp_le_exp] at h3
    push_cast at h3
    omega
  obtain ⟨j, hjJ, hjv⟩ := Set.not_subset.mp hJv
  have hmem : a * j ∈ Ideal.span {d} := by
    rw [hJ]
    exact Ideal.mul_mem_mul (Ideal.le_of_dvd hdvda (Ideal.mem_span_singleton_self a)) hjJ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hj0 : j ≠ 0 := fun h => hjv (h ▸ v.asIdeal.zero_mem)
  have hjE : algebraMap (𝓞 E) E j ≠ 0 := fun h =>
    hj0 (IsFractionRing.injective (𝓞 E) E (by rw [h, map_zero]))
  refine ⟨c, j, hjv, ?_⟩
  rw [div_eq_div_iff hdE hjE, ← map_mul, ← map_mul, hc]
private lemma le_one_lemma_2 {E : Type} [Field E] [NumberField E] (w : AbsoluteValue E ℝ)
    (v : HeightOneSpectrum (𝓞 E))
    (hw : ∀ x : 𝓞 E, w (algebraMap (𝓞 E) E x) ≤ 1 ∧ (w (algebraMap (𝓞 E) E x) < 1 ↔ x ∈ v.asIdeal))
    (u : E) : (v.valuation E u ≤ 1 ↔ w u ≤ 1) ∧ (v.valuation E u < 1 ↔ w u < 1) := by
  have hj1 : ∀ j : 𝓞 E, j ∉ v.asIdeal → w (algebraMap (𝓞 E) E j) = 1 := fun j hj =>
    le_antisymm (hw j).1 (not_lt.mp fun h => hj ((hw j).2.mp h))
  have hle : ∀ y : E, v.valuation E y ≤ 1 → w y ≤ 1 := by
    intro y hy
    obtain ⟨c, j, hj, rfl⟩ := frac_lemma' v y hy
    rw [map_div₀, hj1 j hj, div_one]
    exact (hw c).1
  have hlt : ∀ y : E, v.valuation E y < 1 → w y < 1 := by
    intro y hy
    obtain ⟨c, j, hj, rfl⟩ := frac_lemma' v y hy.le
    rw [map_div₀, hj1 j hj, div_one]
    apply (hw c).2.mpr
    have hj1' : v.intValuation j = 1 := le_antisymm (v.intValuation_le_one j)
      (not_lt.mp fun h => hj ((v.intValuation_lt_one_iff_mem j).mp h))
    rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      hj1', div_one] at hy
    exact (v.intValuation_lt_one_iff_mem c).mp hy
  by_cases hu0 : u = 0
  · subst hu0; simp
  have hnpos : 0 < w u := w.pos hu0
  constructor
  · refine ⟨hle u, fun h => ?_⟩
    by_contra hn
    push_neg at hn
    have h1 : v.valuation E u⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hn
    have h2 := hlt _ h1
    rw [map_inv₀] at h2
    exact absurd h (not_le.mpr ((inv_lt_one₀ hnpos).mp h2))
  · refine ⟨hlt u, fun h => ?_⟩
    by_contra hn
    push_neg at hn
    have h1 : v.valuation E u⁻¹ ≤ 1 := by rw [map_inv₀]; exact inv_le_one_of_one_le₀ hn
    have h2 := hle _ h1
    rw [map_inv₀] at h2
    exact absurd h (not_lt.mpr ((inv_le_one₀ hnpos).mp h2))
end PI.CompDegEF
end

set_option autoImplicit false
open PI PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc
namespace PI.CompDegEF
theorem _root_.solution : KerProp := by
  intro l _ E _ _ φ v hv hφ x
  have hl0 : ((l : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have key := (le_one_lemma_2 (normAbv φ) v (fun y => hφ y) (algebraMap (𝓞 E) E x / ((l : ℕ) : E))).1
  rw [← Ideal.dvd_span_singleton, ← v.intValuation_le_pow_iff_dvd, ← intValuation_natCast v hv]
  have hvl : 0 < v.intValuation ((l : ℕ) : 𝓞 E) := by
    rw [intValuation_natCast v hv]; exact zero_lt_iff.mpr WithZero.exp_ne_zero
  have hnl : 0 < ‖((l : ℕ) : Om l)‖ := by
    rw [← map_natCast φ]; exact norm_pos_iff.mpr ((map_ne_zero φ).mpr hl0)
  rw [← div_le_one₀ hvl, ← div_le_one hnl]
  have e1 : v.intValuation x / v.intValuation ((l : ℕ) : 𝓞 E) =
      v.valuation E (algebraMap (𝓞 E) E x / ((l : ℕ) : E)) := by
    rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, ← map_natCast (algebraMap (𝓞 E) E) l,
      HeightOneSpectrum.valuation_of_algebraMap]
  have e2 : ‖φ (x : E)‖ / ‖((l : ℕ) : Om l)‖ = normAbv φ (algebraMap (𝓞 E) E x / ((l : ℕ) : E)) := by
    rw [normAbv_apply, map_div₀, norm_div, map_natCast]
  rw [e1, e2]
  exact key.symm
end PI.CompDegEF
