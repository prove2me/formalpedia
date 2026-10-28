-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P06.thermalMixture_identity
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T06:10:12.400816+00:00
-- url     : https://prove2.me/submissions/263725bc-6647-4f6d-974a-6a27d5f0cb87

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P06
open MeasureTheory

namespace M30Aux

lemma gauss_int (c : ℝ) (hc : 0 < c) (k : ℕ) :
    ∫ z : ℂ, ‖z‖ ^ k * Real.exp (-c * ‖z‖ ^ 2) =
      Real.pi * c ^ (-((k : ℝ) + 2) / 2) * Real.Gamma (((k : ℝ) + 2) / 2) := by
  have h := Complex.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (k : ℝ)) (b := c)
    (by norm_num) (by have := (Nat.cast_nonneg k : (0:ℝ) ≤ k); linarith) hc
  simp only [Real.rpow_natCast] at h
  have h2 : ∀ x : ℂ, ‖x‖ ^ (2:ℝ) = ‖x‖ ^ (2:ℕ) := fun x => by
    rw [← Real.rpow_natCast]; norm_num
  simp only [h2] at h
  rw [h]; ring

lemma gauss_integrable (c : ℝ) (hc : 0 < c) (k : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ k * Real.exp (-c * ‖z‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [gauss_int c hc k]
  have : 0 < Real.Gamma (((k : ℝ) + 2) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have : 0 < c ^ (-((k : ℝ) + 2) / 2) := Real.rpow_pos_of_pos hc _
  have := Real.pi_pos
  positivity

lemma gauss_moment (c : ℝ) (hc : 0 < c) (p : ℕ) :
    ∫ z : ℂ, ‖z‖ ^ (2 * p) * Real.exp (-c * ‖z‖ ^ 2) =
      Real.pi * (p.factorial : ℝ) / c ^ (p + 1) := by
  rw [gauss_int c hc]
  have e1 : (((2 * p : ℕ) : ℝ) + 2) / 2 = (p : ℝ) + 1 := by push_cast; ring
  have e2 : -(((2 * p : ℕ) : ℝ) + 2) / 2 = -(((p + 1 : ℕ) : ℝ)) := by push_cast; ring
  rw [e1, e2, Real.Gamma_nat_eq_factorial, Real.rpow_neg hc.le, Real.rpow_natCast]
  field_simp

lemma rot_invariant (F : ℂ → ℂ) (a : Circle) :
    ∫ z : ℂ, F (a * z) = ∫ z : ℂ, F z := by
  have hmp := LinearIsometryEquiv.measurePreserving (rotation a)
  have := hmp.integral_comp (rotation a).toHomeomorph.measurableEmbedding F
  simpa [rotation_apply] using this

lemma cmoment_off (c : ℝ) (p q : ℕ) (hpq : p ≠ q) :
    ∫ z : ℂ, ((Real.exp (-c * ‖z‖ ^ 2) : ℝ) : ℂ) * z ^ p * (starRingEnd ℂ z) ^ q = 0 := by
  set I0 := ∫ z : ℂ, ((Real.exp (-c * ‖z‖ ^ 2) : ℝ) : ℂ) * z ^ p * (starRingEnd ℂ z) ^ q
  have hd : ((p : ℝ) - q) ≠ 0 := by
    intro h; apply hpq; exact_mod_cast sub_eq_zero.mp h
  set t : ℝ := Real.pi / ((p : ℝ) - q)
  let a : Circle := Circle.exp t
  have ha : (a : ℂ) = Complex.exp (t * Complex.I) := Circle.coe_exp t
  have hfac : (a : ℂ) ^ p * (starRingEnd ℂ (a : ℂ)) ^ q = -1 := by
    rw [ha, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
      ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    have : (p : ℂ) * (t * Complex.I) + (q : ℂ) * (t * -Complex.I) =
        ((((p : ℝ) - q) * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, show ((p : ℝ) - q) * t = Real.pi by simp only [t]; field_simp]
    exact Complex.exp_pi_mul_I
  have key := rot_invariant (fun z => ((Real.exp (-c * ‖z‖ ^ 2) : ℝ) : ℂ) * z ^ p *
      (starRingEnd ℂ z) ^ q) a
  have hrw : ∀ z : ℂ, ((Real.exp (-c * ‖(a : ℂ) * z‖ ^ 2) : ℝ) : ℂ) * ((a : ℂ) * z) ^ p *
      (starRingEnd ℂ ((a : ℂ) * z)) ^ q =
      ((a : ℂ) ^ p * (starRingEnd ℂ (a : ℂ)) ^ q) *
        (((Real.exp (-c * ‖z‖ ^ 2) : ℝ) : ℂ) * z ^ p * (starRingEnd ℂ z) ^ q) := by
    intro z
    rw [norm_mul, Circle.norm_coe, one_mul, map_mul, mul_pow, mul_pow]; ring
  simp only [hrw, hfac, integral_const_mul] at key
  have : I0 = -I0 := by simpa [I0] using key.symm
  have h2 : (2 : ℂ) * I0 = 0 := by linear_combination this
  simpa using h2


lemma cmoment_diag (c : ℝ) (hc : 0 < c) (p : ℕ) :
    ∫ z : ℂ, ((Real.exp (-c * ‖z‖ ^ 2) : ℝ) : ℂ) * z ^ p * (starRingEnd ℂ z) ^ p =
      ((Real.pi * (p.factorial : ℝ) / c ^ (p + 1) : ℝ) : ℂ) := by
  have : ∀ z : ℂ, ((Real.exp (-c * ‖z‖ ^ 2) : ℝ) : ℂ) * z ^ p * (starRingEnd ℂ z) ^ p =
      ((‖z‖ ^ (2 * p) * Real.exp (-c * ‖z‖ ^ 2) : ℝ) : ℂ) := by
    intro z
    rw [mul_assoc, ← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  simp only [this, integral_complex_ofReal, gauss_moment c hc]

lemma cmoment_integrable (c : ℝ) (hc : 0 < c) (p q : ℕ) :
    Integrable (fun z : ℂ => ((Real.exp (-c * ‖z‖ ^ 2) : ℝ) : ℂ) * z ^ p * (starRingEnd ℂ z) ^ q) := by
  refine (gauss_integrable c hc (p + q)).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact (by fun_prop : Continuous (fun z : ℂ => ((Real.exp (-c * ‖z‖ ^ 2) : ℝ) : ℂ) * z ^ p *
      (starRingEnd ℂ z) ^ q)).aestronglyMeasurable
  · rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le, pow_add]
    exact le_of_eq (by ring)

/-- the moment integrand -/
noncomputable def Phi (s : ℝ) (p q : ℕ) (z : ℂ) : ℂ :=
  ((Real.exp (-s * ‖z‖ ^ 2) : ℝ) : ℂ) * z ^ p * (starRingEnd ℂ z) ^ q

open QAlgorithms.Papers.Independent.Next46.P32 in
lemma cn_moment (N s : ℝ) (hN : 0 ≤ N) (hs : 0 ≤ s) (p q : ℕ) :
    Integrable (Phi s p q) (complexNormal N 0) ∧
    ∫ z, Phi s p q z ∂(complexNormal N 0) =
      if p = q then (((p.factorial : ℝ) * N ^ p / (1 + s * N) ^ (p + 1) : ℝ) : ℂ) else 0 := by
  rcases hN.eq_or_lt with h0 | hpos
  · subst h0
    simp only [complexNormal, if_true]
    refine ⟨integrable_dirac (by simp), ?_⟩
    rw [integral_dirac]
    simp only [Phi]
    rcases Nat.eq_zero_or_pos p with hp | hp <;> rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hp; subst hq; simp
    · subst hp; simp [zero_pow hq.ne']; omega
    · simp [zero_pow hp.ne']
    · simp [zero_pow hp.ne']
  · have hN0 : N ≠ 0 := hpos.ne'
    set ρ : ℂ → ℝ := fun z => Real.exp (-Complex.normSq (z - 0) / N) / (Real.pi * N) with hρ
    have hcn : complexNormal N 0 = volume.withDensity (fun z => ENNReal.ofReal (ρ z)) := by
      simp only [complexNormal, hN0, if_false, ρ]
    have hmeas : Measurable (fun z => ENNReal.ofReal (ρ z)) := by
      apply ENNReal.measurable_ofReal.comp; simp only [ρ]; fun_prop
    have hfin : ∀ᵐ z ∂(volume : Measure ℂ), ENNReal.ofReal (ρ z) < ⊤ :=
      Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    have hρnn : ∀ z, 0 ≤ ρ z := fun z => by simp only [ρ]; positivity
    have hsm : ∀ z, (ENNReal.ofReal (ρ z)).toReal • Phi s p q z =
        (((Real.pi * N)⁻¹ : ℝ) : ℂ) * Phi (s + 1 / N) p q z := by
      intro z
      rw [ENNReal.toReal_ofReal (hρnn z), Complex.real_smul]
      simp only [ρ, Phi, sub_zero, Complex.normSq_eq_norm_sq]
      have : Real.exp (-(s + 1 / N) * ‖z‖ ^ 2) = Real.exp (-s * ‖z‖ ^ 2) * Real.exp (-‖z‖ ^ 2 / N) := by
        rw [← Real.exp_add]; congr 1; field_simp; ring
      rw [this]; push_cast; ring
    have hc : 0 < s + 1 / N := by positivity
    refine ⟨?_, ?_⟩
    · rw [hcn, integrable_withDensity_iff_integrable_smul' hmeas hfin]
      simp only [hsm]
      exact (cmoment_integrable _ hc p q).const_mul _
    · rw [hcn, integral_withDensity_eq_integral_toReal_smul hmeas hfin]
      simp only [hsm, integral_const_mul]
      split_ifs with hpq
      · subst hpq
        simp only [Phi]
        rw [cmoment_diag _ hc, ← Complex.ofReal_mul]
        congr 1
        have : s + 1 / N = (1 + s * N) / N := by field_simp; ring
        rw [this, div_pow]
        have : 0 < 1 + s * N := by positivity
        have := Real.pi_pos
        field_simp
        ring
      · simp only [Phi]; rw [cmoment_off _ p q hpq, mul_zero]


lemma Phi_zero (p q : ℕ) (z : ℂ) : Phi 0 p q z = z ^ p * (starRingEnd ℂ z) ^ q := by
  simp [Phi]

lemma thermal_isDensity (N : ℝ) (hN : 0 ≤ N) :
    QAlgorithms.Papers.Independent.Dependency50.P33.IsDensity
      (QAlgorithms.Papers.Independent.Next46.P32.identicalThermalKernel 1 N) := by
  classical
  set r : ℝ := N / (N + 1) with hr
  have hN1 : 0 < N + 1 := by linarith
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one hN1]; linarith
  set pr : ℕ → ℝ := fun n => r ^ n / (N + 1) with hpr
  have hpr0 : ∀ n, 0 ≤ pr n := fun n => by positivity
  have hsum : Summable pr := (summable_geometric_of_lt_one hr0 hr1).div_const _
  have htsum : ∑' n, pr n = 1 := by
    rw [hpr, tsum_div_const, tsum_geometric_of_lt_one hr0 hr1]
    rw [hr]; field_simp; ring
  have hX : ∀ i j : Fin 1 → ℕ,
      QAlgorithms.Papers.Independent.Next46.P32.identicalThermalKernel 1 N i j =
        if i = j then ((pr (i 0) : ℝ) : ℂ) else 0 := by
    intro i j
    simp [QAlgorithms.Papers.Independent.Next46.P32.identicalThermalKernel, pr, r]
  have hconst : ∀ i : Fin 1 → ℕ, (fun _ : Fin 1 => i 0) = i := by
    intro i; funext k; rw [Subsingleton.elim k 0]
  refine ⟨⟨{ left := fun n => lp.single 2 (fun _ : Fin 1 => n) ((pr n : ℝ) : ℂ),
              right := fun n => lp.single 2 (fun _ : Fin 1 => n) (1 : ℂ),
              summable := ?_,
              coefficients := ?_ }⟩, ?_, ?_, ?_⟩
  · have h2 : (0 : ENNReal) < 2 := by norm_num
    simp only [lp.norm_single h2, norm_one, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (hpr0 _)]
    exact hsum
  · intro i j
    rw [hX, tsum_eq_single (i 0)]
    · rw [hconst i]
      simp only [lp.single_apply, Pi.single_eq_same]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, Pi.single_eq_of_ne' hij]; simp
    · intro n hn
      have : (fun _ : Fin 1 => n) ≠ i := by
        intro h; apply hn; rw [← h]
      simp only [lp.single_apply, Pi.single_eq_of_ne' this, zero_mul]
  · intro s z
    have : (∑ i ∈ s, ∑ j ∈ s, star (z i) *
        QAlgorithms.Papers.Independent.Next46.P32.identicalThermalKernel 1 N i j * z j) =
        ∑ i ∈ s, ((pr (i 0) * Complex.normSq (z i) : ℝ) : ℂ) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [hX, mul_ite, ite_mul, mul_zero, zero_mul]
      rw [Finset.sum_ite_eq s i, if_pos hi]
      push_cast; rw [Complex.normSq_eq_conj_mul_self]; simp only [Complex.star_def]; ring
    rw [this, ← Complex.ofReal_sum]
    refine ⟨Complex.ofReal_im _, ?_⟩
    rw [Complex.ofReal_re]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hpr0 _) (Complex.normSq_nonneg _)
  · have : (fun i : Fin 1 → ℕ =>
        (QAlgorithms.Papers.Independent.Next46.P32.identicalThermalKernel 1 N i i).re) =
        pr ∘ (Equiv.funUnique (Fin 1) ℕ) := by
      funext i; simp [hX]
    rw [this]; exact (Equiv.summable_iff _).mpr hsum
  · have : (fun i : Fin 1 → ℕ =>
        (QAlgorithms.Papers.Independent.Next46.P32.identicalThermalKernel 1 N i i).re) =
        pr ∘ (Equiv.funUnique (Fin 1) ℕ) := by
      funext i; simp [hX]
    rw [this, Function.comp_def, Equiv.tsum_eq (Equiv.funUnique (Fin 1) ℕ) pr, htsum]

end M30Aux

namespace M30Aux
open QAlgorithms.Papers.Independent.Next46.P32 in
lemma pck_eq (α : ℂ) (a b : NumberString 1) :
    productCoherentKernel 1 (fun _ => α) a b =
      (((Real.sqrt ((a 0).factorial : ℝ) * Real.sqrt ((b 0).factorial : ℝ))⁻¹ : ℝ) : ℂ) *
        Phi 1 (a 0) (b 0) α := by
  simp only [productCoherentKernel, QAlgorithms.Papers.Independent.Dependency50.P39.coherentCoefficient,
    Fin.prod_univ_one, Phi]
  have he : Real.exp (-1 * ‖α‖ ^ 2) = Real.exp (-Complex.normSq α / 2) * Real.exp (-Complex.normSq α / 2) := by
    rw [← Real.exp_add, Complex.normSq_eq_norm_sq]; congr 1; ring
  rw [he]
  simp only [star_div₀, star_mul', Complex.star_def, Complex.conj_ofReal, map_pow]
  push_cast
  field_simp
end M30Aux

noncomputable section

open QAlgorithms.Papers.Independent.Support50.P06

open MeasureTheory Filter

open scoped ENNReal BigOperators Topology

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)

open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel identicalThermalKernel vacuum productCoherentKernel
   jointMix bobMarginal charlieMarginal pureLoss broadcast mixedOutput
   spectralEntropyNats FockPOVM realFockTracePair modeEnergy complexNormal
   StrongConjecture2)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, (18)–(19): the same normalized thermal density is the Gaussian
coherent mixture and the geometric photon-number mixture. Integrability and
probability normalization are conclusions. N=0 uses delta_0, since the printed
Lebesgue density is singular there; the photon representation fixes this limit. -/
theorem solution (N : ℝ) (hN : 0 ≤ N) :
    IsProbabilityMeasure (complexNormal N 0) ∧
    Integrable (fun alpha : ℂ => alpha) (complexNormal N 0) ∧
    (∫ alpha : ℂ, alpha ∂complexNormal N 0) = 0 ∧
    Integrable (fun alpha : ℂ => Complex.normSq alpha) (complexNormal N 0) ∧
    (∫ alpha : ℂ, Complex.normSq alpha ∂complexNormal N 0) = N ∧
    IsDensity (identicalThermalKernel 1 N) ∧
    coherentMixture N = identicalThermalKernel 1 N ∧
    (∀ a b : NumberString 1,
      Integrable (fun alpha : ℂ => productCoherentKernel 1 (fun _ => alpha) a b)
        (complexNormal N 0) ∧
      identicalThermalKernel 1 N a b = ∑' j : ℕ,
        ((N ^ j / (N + 1) ^ (j + 1) : ℝ) : ℂ) *
          (if a = (fun _ => j) ∧ b = (fun _ => j) then 1 else 0)) := by
  have hM := fun s hs p q => M30Aux.cn_moment N s hN hs p q
  have hf00 : M30Aux.Phi 0 0 0 = fun _ => (1:ℂ) := by funext z; simp [M30Aux.Phi]
  have hf10 : M30Aux.Phi 0 1 0 = fun z => z := by funext z; simp [M30Aux.Phi]
  have hf11 : M30Aux.Phi 0 1 1 = fun z => ((Complex.normSq z : ℝ) : ℂ) := by
    funext z; simp [M30Aux.Phi, Complex.mul_conj]
  have hI00 := hM 0 le_rfl 0 0
  have hI10 := hM 0 le_rfl 1 0
  have hI11 := hM 0 le_rfl 1 1
  rw [hf00] at hI00
  rw [hf10] at hI10
  rw [hf11] at hI11
  have hconst : ∀ i : NumberString 1, (fun _ : Fin 1 => i 0) = i := by
    intro i; funext k; rw [Subsingleton.elim k 0]
  have hext : ∀ a b : NumberString 1, a = b ↔ a 0 = b 0 := by
    intro a b; constructor
    · intro h; rw [h]
    · intro h; rw [← hconst a, ← hconst b, h]
  have hth : ∀ a b : NumberString 1, identicalThermalKernel 1 N a b =
      if a 0 = b 0 then ((((N / (N + 1)) ^ (a 0) / (N + 1)) : ℝ) : ℂ) else 0 := by
    intro a b
    simp only [identicalThermalKernel, Fin.prod_univ_one, hext a b]
  have hval : ∀ p : ℕ, ((Real.sqrt (p.factorial : ℝ) * Real.sqrt (p.factorial : ℝ))⁻¹) *
      ((p.factorial : ℝ) * N ^ p / (1 + 1 * N) ^ (p + 1)) = (N / (N + 1)) ^ p / (N + 1) := by
    intro p
    rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
    have : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
    have : 0 < N + 1 := by linarith
    rw [div_pow, pow_succ]
    field_simp
    ring
  have hcoh : coherentMixture N = identicalThermalKernel 1 N := by
    funext a b
    simp only [coherentMixture, M30Aux.pck_eq, integral_const_mul]
    rw [(hM 1 zero_le_one (a 0) (b 0)).2, hth]
    split_ifs with h
    · rw [← h, ← Complex.ofReal_mul, hval]
    · rw [mul_zero]
  refine ⟨?_, hI10.1, ?_, ?_, ?_, M30Aux.thermal_isDensity N hN, hcoh, ?_⟩
  · have hfin : IsFiniteMeasure (complexNormal N 0) := by
      rcases (integrable_const_iff.mp hI00.1) with h | h
      · exact absurd h one_ne_zero
      · exact h
    constructor
    have h := hI00.2
    rw [integral_const, if_pos rfl] at h
    simp at h
    rw [measureReal_def, ENNReal.toReal_eq_one_iff] at h
    exact h
  · simpa using hI10.2
  · have := hI11.1.re
    simpa using this
  · have h := hI11.2
    rw [integral_complex_ofReal] at h
    simp at h
    exact_mod_cast h
  · intro a b
    refine ⟨?_, ?_⟩
    · simp only [M30Aux.pck_eq]
      exact (hM 1 zero_le_one (a 0) (b 0)).1.const_mul _
    · rw [tsum_eq_single (a 0)]
      · rw [hth]
        have : (a = (fun _ => a 0) ∧ b = (fun _ => a 0)) ↔ a 0 = b 0 := by
          rw [hconst a]; constructor
          · rintro ⟨-, h⟩; rw [h]
          · intro h; exact ⟨rfl, by rw [hext]; exact h.symm⟩
        simp only [this]
        split_ifs
        · rw [mul_one]; congr 1; rw [div_pow, div_div, pow_succ]
        · rw [mul_zero]
      · intro j hj
        have : ¬ (a = (fun _ => j) ∧ b = (fun _ => j)) := by
          rintro ⟨h, -⟩; apply hj; rw [h]
        rw [if_neg this, mul_zero]



end

