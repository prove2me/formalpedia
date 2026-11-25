-- Prove2me | solution 1 for UpperTheory.isIntegral_cmType_unitaryPart_mul_absNorm_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:03:31.525057+00:00
-- url     : https://prove2.me/submissions/511e0cc8-a5aa-46ba-bfef-50f5cea93677

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharProd
import Definitions.Def_Development_AutomorphicArithmetic_DivisorFrames_IsIntegralCmTypeUnitaryPartMulAbsNormPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain
private lemma isIntegral_pow_div_mul_pow (a b : ℂ) (ha : IsIntegral ℤ a) (hb : IsIntegral ℤ b) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (n : ℤ) (M : ℕ) (hn : n.natAbs ≤ M) :
    IsIntegral ℤ ((a / b) ^ n * (a * b) ^ M) := by
  have hbk : ∀ k : ℕ, b ^ k * b⁻¹ ^ k = 1 := fun k => by rw [← mul_pow, mul_inv_cancel₀ hb0, one_pow]
  have hak : ∀ k : ℕ, a ^ k * a⁻¹ ^ k = 1 := fun k => by rw [← mul_pow, mul_inv_cancel₀ ha0, one_pow]
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simp only [Int.natAbs_natCast] at hn
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
    have e : (a / b) ^ (k : ℤ) * (a * b) ^ (k + d) = a ^ (k + k + d) * b ^ d * (b ^ k * b⁻¹ ^ k) := by
      rw [zpow_natCast, div_eq_mul_inv]
      ring
    rw [e, hbk, mul_one]
    exact (ha.pow _).mul (hb.pow _)
  · simp only [Int.natAbs_neg, Int.natAbs_natCast] at hn
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
    have e : (a / b) ^ (-(k : ℤ)) * (a * b) ^ (k + d) = a ^ d * b ^ (k + k + d) * (a ^ k * a⁻¹ ^ k) := by
      rw [zpow_neg, ← inv_zpow, inv_div, zpow_natCast, div_eq_mul_inv]
      ring
    rw [e, hak, mul_one]
    exact (ha.pow _).mul (hb.pow _)
private lemma div_abs_sq_eq_div_conj (a : ℂ) (ha0 : a ≠ 0) :
    (a / ((‖a‖ : ℝ) : ℂ)) ^ 2 = a / (starRingEnd ℂ) a := by
  have hn : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero, norm_eq_zero]
    exact ha0
  have hc : (starRingEnd ℂ) a ≠ 0 := (map_ne_zero _).mpr ha0
  rw [div_pow, ← Complex.mul_conj' a]
  field_simp
private lemma span_eq_pow_of_valuation_supported_at (E : Type) [Field E] [NumberField E]
    (P : HeightOneSpectrum (𝓞 E)) (h : ℕ) (a : 𝓞 E) (ha : a ≠ 0)
    (h1 : P.valuation E (a : E) = WithZero.exp (-(h : ℤ)))
    (h2 : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.valuation E (a : E) = 1) :
    Ideal.span {a} = P.asIdeal ^ h := by
  have h1' : P.intValuation a = WithZero.exp (-(h : ℤ)) := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    exact h1
  have h2' : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.intValuation a = 1 := by
    intro Q hQ
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    exact h2 Q hQ
  obtain ⟨J, hJ⟩ := (P.intValuation_le_pow_iff_dvd a h).mp h1'.le
  rw [hJ]
  suffices hJt : J = ⊤ by rw [hJt, Ideal.mul_top]
  by_contra hne
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hne
  have hspan0 : Ideal.span {a} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact ha
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at hJ
    exact hspan0 hJ
  have hM0 : M ≠ ⊥ := fun hb => hJ0 (le_bot_iff.mp (hb ▸ hJM))
  let Q : HeightOneSpectrum (𝓞 E) := ⟨M, hM.isPrime, hM0⟩
  have hQJ : Q.asIdeal ∣ J := Ideal.dvd_iff_le.mpr hJM
  by_cases hQP : Q = P
  · have hPJ : P.asIdeal ∣ J := hQP ▸ hQJ
    have hdvd : P.asIdeal ^ (h + 1) ∣ Ideal.span {a} := by
      rw [hJ, pow_succ]
      exact mul_dvd_mul_left _ hPJ
    have hv := (P.intValuation_le_pow_iff_dvd a (h + 1)).mpr hdvd
    rw [h1', WithZero.exp_le_exp] at hv
    push_cast at hv
    omega
  · have hlt : Q.intValuation a < 1 := by
      rw [Q.intValuation_lt_one_iff_dvd, hJ]
      exact dvd_mul_of_dvd_right hQJ _
    rw [h2' Q hQP] at hlt
    exact lt_irrefl _ hlt
private lemma absNorm_span_sq_eq_prod_embeddings_sq (E : Type) [Field E] [NumberField E] (a : 𝓞 E) :
    ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℂ) ^ 2 = (∏ σ : E →+* ℂ, σ (a : E)) ^ 2 := by
  rw [Ideal.absNorm_span_singleton]
  have h1 : ((((Algebra.norm ℤ) a).natAbs : ℕ) : ℂ) ^ 2 = (((Algebra.norm ℤ a : ℤ)) : ℂ) ^ 2 := by
    rw [← Int.cast_natCast, ← Int.cast_pow, Int.natAbs_sq, Int.cast_pow]
  rw [h1]
  congr 1
  have h2 : (((Algebra.norm ℤ a : ℤ)) : ℂ) = algebraMap ℚ ℂ (Algebra.norm ℚ (a : E)) := by
    rw [← Algebra.coe_norm_int]
    simp
  rw [h2, Algebra.norm_eq_prod_embeddings ℚ ℂ]
  exact Fintype.prod_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ (fun σ => rfl)
end

set_option autoImplicit false
open NumberField IsDedekindDomain
namespace UpperTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), Function.Injective (Sum.elim φ fun i => ComplexEmbedding.conjugate (φ i)) → ∀ (n : I → ℤ) (M : ℕ), (∀ i, (n i).natAbs ≤ M) → ∀ (P : HeightOneSpectrum (𝓞 E)) (h : ℕ) (z : Eˣ), P.valuation E (z : E) = WithZero.exp (-(h : ℤ)) → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.valuation E (z : E) = 1) → IsIntegral ℤ ((∏ i, (φ i (z : E) / ((‖φ i (z : E)‖ : ℝ) : ℂ)) ^ n i) * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (h * M)) := by
  intro E _ _ I _ φ hinj n M hn P h z hP hQ
  classical
  have hle : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (z : E) ≤ 1 := by
    intro v
    by_cases hv : v = P
    · subst hv
      rw [hP, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    · rw [hQ v hv]
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (z : E) hle
  have hza : (z : E) = (a : E) := ha.symm
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact z.ne_zero ha.symm
  have hspan := span_eq_pow_of_valuation_supported_at E P h a ha0 (by rw [← hza]; exact hP) (fun Q hQP => by rw [← hza]; exact hQ Q hQP)
  have hnorm : ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (2 * h) = (∏ σ : E →+* ℂ, σ (a : E)) ^ 2 := by
    rw [← absNorm_span_sq_eq_prod_embeddings_sq E a, hspan, map_pow]
    push_cast
    ring
  have haE : (a : E) ≠ 0 := hza ▸ z.ne_zero
  have hint : ∀ σ : E →+* ℂ, IsIntegral ℤ (σ (a : E)) := fun σ =>
    (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
  have hw0 : ∀ i, φ i (a : E) ≠ 0 := fun i => (map_ne_zero _).mpr haE
  have hwc0 : ∀ i, (starRingEnd ℂ) (φ i (a : E)) ≠ 0 := fun i => (map_ne_zero _).mpr (hw0 i)
  have hzp : ∀ (x : ℂ) (k : ℤ), (x ^ k) ^ 2 = (x ^ 2) ^ k := fun x k => by
    rw [← zpow_natCast, ← zpow_natCast x, ← zpow_mul, ← zpow_mul, mul_comm]
  rw [hza]
  apply IsIntegral.of_pow (n := 2) two_pos
  have e1 : ((∏ i, (φ i (a : E) / ((‖φ i (a : E)‖ : ℝ) : ℂ)) ^ n i) * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (h * M)) ^ 2
      = (∏ i, (φ i (a : E) / (starRingEnd ℂ) (φ i (a : E))) ^ n i) * ((∏ σ : E →+* ℂ, σ (a : E)) ^ 2) ^ M := by
    rw [mul_pow, ← Finset.prod_pow, ← hnorm]
    congr 1
    · apply Finset.prod_congr rfl
      intro i _
      rw [hzp, div_abs_sq_eq_div_conj _ (hw0 i)]
    · ring
  let e : I ⊕ I ↪ (E →+* ℂ) := ⟨Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i)), hinj⟩
  have hsplit : ∏ σ : E →+* ℂ, σ (a : E)
      = (∏ i, φ i (a : E) * (starRingEnd ℂ) (φ i (a : E))) * ∏ σ ∈ Finset.univ \ Finset.univ.map e, σ (a : E) := by
    rw [← Finset.prod_sdiff (Finset.subset_univ (Finset.univ.map e)), Finset.prod_map, Fintype.prod_sum_type,
      ← Finset.prod_mul_distrib, mul_comm]
    rfl
  rw [e1, hsplit]
  have e2 : (∏ i, (φ i (a : E) / (starRingEnd ℂ) (φ i (a : E))) ^ n i) *
      (((∏ i, φ i (a : E) * (starRingEnd ℂ) (φ i (a : E))) * ∏ σ ∈ Finset.univ \ Finset.univ.map e, σ (a : E)) ^ 2) ^ M
      = (∏ i, (φ i (a : E) / (starRingEnd ℂ) (φ i (a : E))) ^ n i * (φ i (a : E) * (starRingEnd ℂ) (φ i (a : E))) ^ (2 * M))
        * (∏ σ ∈ Finset.univ \ Finset.univ.map e, σ (a : E)) ^ (2 * M) := by
    simp only [Finset.prod_mul_distrib, Finset.prod_pow]
    ring
  rw [e2]
  apply IsIntegral.mul
  · apply IsIntegral.prod
    intro i _
    exact isIntegral_pow_div_mul_pow _ _ (hint (φ i)) (hint (ComplexEmbedding.conjugate (φ i))) (hw0 i) (hwc0 i) (n i) (2 * M)
      (by have := hn i; omega)
  · apply IsIntegral.pow
    apply IsIntegral.prod
    intro σ _
    exact hint σ
end UpperTheory
