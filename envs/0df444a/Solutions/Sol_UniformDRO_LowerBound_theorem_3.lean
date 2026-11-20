-- Prove2me | solution 1 for UniformDRO.LowerBound.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T16:18:02.094198+00:00
-- url     : https://prove2.me/submissions/694d4328-cf4d-415e-9f77-6e50f963bf87

import Mathlib
import Definitions.Def_UniformDRO_LowerBound_Setting
import Definitions.Def_bernoulliRelativeEntropy

open MeasureTheory UniformDRO.LowerBound

lemma tp_integral (z₀ z₁ p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (g : ℝ → ℝ) :
    Integrable g (twoPointLaw z₀ z₁ p) ∧
    ∫ x, g x ∂(twoPointLaw z₀ z₁ p) = (1 - p) * g z₀ + p * g z₁ := by
  have i0 : Integrable g (Measure.dirac z₀) := integrable_dirac (by simp)
  have i1 : Integrable g (Measure.dirac z₁) := integrable_dirac (by simp)
  refine ⟨(i0.smul_measure ENNReal.ofReal_ne_top).add_measure (i1.smul_measure ENNReal.ofReal_ne_top), ?_⟩
  rw [twoPointLaw, integral_add_measure (i0.smul_measure ENNReal.ofReal_ne_top)
    (i1.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hp0]
  simp [smul_eq_mul]

lemma tp_lintegral (z₀ z₁ p : ℝ) (g : ℝ → ENNReal) :
    ∫⁻ x, g x ∂(twoPointLaw z₀ z₁ p) = ENNReal.ofReal (1 - p) * g z₀ + ENNReal.ofReal p * g z₁ := by
  rw [twoPointLaw, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac]
  simp [smul_eq_mul]


lemma cr_nonneg (k t : ℝ) (hk : 1 < k) (ht : 0 ≤ t) : 0 ≤ UniformDRO.Concentration.cressieRead k t := by
  unfold UniformDRO.Concentration.cressieRead
  apply div_nonneg _ (by nlinarith)
  have := one_add_mul_self_le_rpow_one_add (show (-1 : ℝ) ≤ t - 1 by linarith) hk.le
  rw [show 1 + (t - 1) = t by ring] at this
  linarith

theorem r12a (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (z₀ z₁ p : ℝ) (hz : z₀ ≤ z₁)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hpk : pk k ρ ≤ p) :
    UniformDRO.Concentration.robustRisk k ρ (twoPointLaw z₀ z₁ p) id = z₁ := by
  classical
  obtain ⟨hp0, hp1⟩ := hp
  set c := 1 + k * (k - 1) * ρ with hc
  have hc0 : 0 < c := by
    have : 0 < k * (k - 1) * ρ := mul_pos (mul_pos (by linarith) (by linarith)) hρ
    linarith
  have hpk0 : 0 < pk k ρ := Real.rpow_pos_of_pos hc0 _
  have hppos : 0 < p := lt_of_lt_of_le hpk0 hpk
  unfold UniformDRO.Concentration.robustRisk
  apply IsGreatest.csSup_eq
  refine ⟨?_, ?_⟩
  · by_cases hzz : z₀ = z₁
    · -- L ≡ 1
      refine ⟨fun _ => 1, measurable_const, fun _ => zero_le_one, (tp_integral z₀ z₁ p hp0 hp1 _).1,
        ?_, (tp_integral z₀ z₁ p hp0 hp1 _).1, ?_, ?_⟩
      · rw [(tp_integral z₀ z₁ p hp0 hp1 _).2]; ring
      · rw [tp_lintegral]
        simp [UniformDRO.Concentration.cressieRead]
      · rw [(tp_integral z₀ z₁ p hp0 hp1 _).2, hzz]; simp; ring
    · -- all mass on z₁
      set L : ℝ → ℝ := fun x => if x = z₁ then 1 / p else 0 with hL
      have hLm : Measurable L := Measurable.ite (measurableSet_singleton z₁) measurable_const measurable_const
      have hL0 : L z₀ = 0 := by simp [hL, hzz]
      have hL1 : L z₁ = 1 / p := by simp [hL]
      refine ⟨L, hLm, fun x => by simp only [hL]; split_ifs <;> positivity,
        (tp_integral z₀ z₁ p hp0 hp1 _).1, ?_, (tp_integral z₀ z₁ p hp0 hp1 _).1, ?_, ?_⟩
      · rw [(tp_integral z₀ z₁ p hp0 hp1 _).2, hL0, hL1]; field_simp; ring
      · rw [tp_lintegral, hL0, hL1]
        have h0 : UniformDRO.Concentration.cressieRead k 0 = 1 / k := by
          unfold UniformDRO.Concentration.cressieRead
          rw [Real.zero_rpow (by linarith)]
          have : k - 1 ≠ 0 := by linarith
          field_simp; ring
        have hX : p * (1 / p) ^ k ≤ c := by
          have e : p * (1 / p) ^ k = p ^ (1 - k) := by
            rw [one_div, Real.inv_rpow hp0, Real.rpow_sub hppos, Real.rpow_one, div_eq_mul_inv]
          rw [e]
          have hmono : p ^ (1 - k) ≤ (pk k ρ) ^ (1 - k) :=
            Real.rpow_le_rpow_of_nonpos hpk0 hpk (by linarith)
          have hpkpow : (pk k ρ) ^ (1 - k) = c := by
            unfold pk
            rw [← hc, ← Real.rpow_mul hc0.le]
            have : -(1 / (k - 1)) * (1 - k) = 1 := by
              have : k - 1 ≠ 0 := by linarith
              field_simp; ring
            rw [this, Real.rpow_one]
          linarith
        have hk1 : k - 1 ≠ 0 := by linarith
        have hval : (1 - p) * UniformDRO.Concentration.cressieRead k 0
            + p * UniformDRO.Concentration.cressieRead k (1 / p)
            = (p * (1 / p) ^ k - 1) / (k * (k - 1)) := by
          rw [h0]; unfold UniformDRO.Concentration.cressieRead
          field_simp; ring
        have hn0 := cr_nonneg k 0 hk le_rfl
        have hn1 := cr_nonneg k (1 / p) hk (by positivity)
        rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hp0,
          ← ENNReal.ofReal_add (by positivity) (by positivity), hval]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ (by nlinarith)]
        nlinarith
      · rw [(tp_integral z₀ z₁ p hp0 hp1 _).2, hL0, hL1]; field_simp; simp
  · rintro v ⟨L, -, hLnn, -, hL1, -, -, rfl⟩
    rw [(tp_integral z₀ z₁ p hp0 hp1 _).2] at hL1 ⊢
    simp only [id]
    have h1p : 0 ≤ 1 - p := by linarith
    have h := congrArg (fun t => t * z₁) hL1
    nlinarith [mul_nonneg (mul_nonneg h1p (hLnn z₀)) (sub_nonneg.mpr hz)]

theorem r12b (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (z₀ z₁ p : ℝ) (hz : z₀ ≤ z₁)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hpk : p ≤ pk k ρ) :
    UniformDRO.Concentration.robustRisk k ρ (twoPointLaw z₀ z₁ p) id ≤
      UniformDRO.Concentration.ck k ρ * p ^ (1 / UniformDRO.Concentration.kstar k) * z₁ + (1 - UniformDRO.Concentration.ck k ρ * p ^ (1 / UniformDRO.Concentration.kstar k)) * z₀ := by
  classical
  obtain ⟨hp0, hp1⟩ := hp
  set c := 1 + k * (k - 1) * ρ with hc
  have hc0 : 0 < c := by
    have : 0 < k * (k - 1) * ρ := mul_pos (mul_pos (by linarith) (by linarith)) hρ
    linarith
  have hk0 : 0 < k := by linarith
  have hk1 : k - 1 ≠ 0 := by linarith
  have hck : UniformDRO.Concentration.ck k ρ = c ^ (1 / k) := rfl
  have hks : 1 / UniformDRO.Concentration.kstar k = 1 - 1 / k := by
    unfold UniformDRO.Concentration.kstar; field_simp
  rw [hck, hks]
  set B := c ^ (1 / k) * p ^ (1 - 1 / k) with hB
  have goal_form : B * z₁ + (1 - B) * z₀ = z₀ + B * (z₁ - z₀) := by ring
  rw [goal_form]
  unfold UniformDRO.Concentration.robustRisk
  apply csSup_le
  · -- L ≡ 1 is feasible
    refine ⟨_, fun _ => 1, measurable_const, fun _ => zero_le_one, (tp_integral z₀ z₁ p hp0 hp1 _).1,
      ?_, (tp_integral z₀ z₁ p hp0 hp1 _).1, ?_, rfl⟩
    · rw [(tp_integral z₀ z₁ p hp0 hp1 _).2]; ring
    · rw [tp_lintegral]; simp [UniformDRO.Concentration.cressieRead]
  · rintro v ⟨L, -, hLnn, -, hL1, -, hdiv, rfl⟩
    rw [(tp_integral z₀ z₁ p hp0 hp1 _).2] at hL1 ⊢
    simp only [id]
    rw [tp_lintegral] at hdiv
    have hf0 := cr_nonneg k (L z₀) hk (hLnn z₀)
    have hf1 := cr_nonneg k (L z₁) hk (hLnn z₁)
    rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hp0,
      ← ENNReal.ofReal_add (by positivity) (by positivity)] at hdiv
    have hdivR := (ENNReal.ofReal_le_ofReal_iff hρ.le).mp hdiv
    -- the k-th moment bound: p L₁^k ≤ c
    have hmom : p * L z₁ ^ k ≤ c := by
      unfold UniformDRO.Concentration.cressieRead at hdivR
      have hkk : 0 < k * (k - 1) := by nlinarith
      have e : (1 - p) * ((L z₀ ^ k - k * L z₀ + k - 1) / (k * (k - 1)))
          + p * ((L z₁ ^ k - k * L z₁ + k - 1) / (k * (k - 1)))
          = ((1 - p) * L z₀ ^ k + p * L z₁ ^ k - k * ((1 - p) * L z₀ + p * L z₁) + (k - 1))
            / (k * (k - 1)) := by ring
      rw [e, hL1, div_le_iff₀ hkk] at hdivR
      have : 0 ≤ (1 - p) * L z₀ ^ k := mul_nonneg (by linarith) (Real.rpow_nonneg (hLnn z₀) _)
      nlinarith
    -- hence p L₁ ≤ B
    have hpL : p * L z₁ ≤ B := by
      rcases hp0.eq_or_lt with h0 | hpos
      · subst h0; simp [hB]; positivity
      have hL1le : L z₁ ≤ c ^ (1 / k) * p ^ (-(1 / k)) := by
        have h1 : L z₁ ^ k ≤ c / p := by rw [le_div_iff₀ hpos]; linarith
        have h2 := Real.rpow_le_rpow (Real.rpow_nonneg (hLnn z₁) _) h1 (by positivity : 0 ≤ 1 / k)
        rw [← Real.rpow_mul (hLnn z₁), mul_one_div_cancel hk0.ne', Real.rpow_one,
          Real.div_rpow hc0.le hpos.le, div_eq_mul_inv, ← Real.rpow_neg hpos.le] at h2
        exact h2
      calc p * L z₁ ≤ p * (c ^ (1 / k) * p ^ (-(1 / k))) := by gcongr
        _ = B := by
          rw [hB, mul_left_comm, ← Real.rpow_one_add' hpos.le (by
            have : 1 / k < 1 := by rw [div_lt_one hk0]; linarith
            linarith)]
          congr 2
    have hdz : 0 ≤ z₁ - z₀ := sub_nonneg.mpr hz
    have hval : (1 - p) * (L z₀ * z₀) + p * (L z₁ * z₁) = z₀ + p * L z₁ * (z₁ - z₀) := by
      have : (1 - p) * L z₀ = 1 - p * L z₁ := by linarith
      calc (1 - p) * (L z₀ * z₀) + p * (L z₁ * z₁) = ((1 - p) * L z₀) * z₀ + p * L z₁ * z₁ := by ring
        _ = (1 - p * L z₁) * z₀ + p * L z₁ * z₁ := by rw [this]
        _ = _ := by ring
    rw [hval]
    nlinarith [mul_le_mul_of_nonneg_right hpL hdz]



lemma sampleProb_nonneg {n : ℕ} (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (b : Fin n → Bool) :
    0 ≤ sampleProb p b := by
  unfold sampleProb
  exact Finset.prod_nonneg (fun i _ => by split_ifs <;> linarith [hp.1, hp.2])

lemma sampleProb_sum {n : ℕ} (p : ℝ) : ∑ b : Fin n → Bool, sampleProb p b = 1 := by
  unfold sampleProb
  rw [← Fintype.prod_sum (fun (_ : Fin n) (x : Bool) => if x then p else 1 - p)]
  simp


theorem leCam (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (M : ℝ) (hM : 0 < M) (n : ℕ)
    (p₀ p₁ δ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0 : ℝ) 1) (hp₁ : p₁ ∈ Set.Icc (0 : ℝ) 1) (hδ : 0 < δ)
    (hsep : 2 * δ ≤ |UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M p₀) id -
      UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M p₁) id|) :
    ENNReal.ofReal (δ / 2 * (1 - tvDist n p₀ p₁)) ≤ minimaxRisk k ρ M n := by
  classical
  set r₀ := UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M p₀) id with hr₀
  set r₁ := UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M p₁) id with hr₁
  unfold minimaxRisk
  refine le_iInf (fun R => ?_)
  set x₀ : (Fin n → Bool) → ℝ := fun b => |R (sampleVec M b) - r₀| with hx₀
  set x₁ : (Fin n → Bool) → ℝ := fun b => |R (sampleVec M b) - r₁| with hx₁
  set P₀ : (Fin n → Bool) → ℝ := fun b => sampleProb p₀ b with hP₀
  set P₁ : (Fin n → Bool) → ℝ := fun b => sampleProb p₁ b with hP₁
  have hE : ∀ (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (r : ℝ),
      r = UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M p) id →
      estRisk k ρ M n R p = ENNReal.ofReal (∑ b, sampleProb p b * |R (sampleVec M b) - r|) := by
    intro p hp r hr
    unfold estRisk
    rw [← hr, ENNReal.ofReal_sum_of_nonneg (fun b _ => mul_nonneg (sampleProb_nonneg p hp b) (abs_nonneg _))]
  have hE0 := hE p₀ hp₀ r₀ hr₀
  have hE1 := hE p₁ hp₁ r₁ hr₁
  have hsup0 : estRisk k ρ M n R p₀ ≤ ⨆ p ∈ Set.Icc (0 : ℝ) 1, estRisk k ρ M n R p :=
    le_iSup₂ (f := fun p (_ : p ∈ Set.Icc (0 : ℝ) 1) => estRisk k ρ M n R p) p₀ hp₀
  have hsup1 : estRisk k ρ M n R p₁ ≤ ⨆ p ∈ Set.Icc (0 : ℝ) 1, estRisk k ρ M n R p :=
    le_iSup₂ (f := fun p (_ : p ∈ Set.Icc (0 : ℝ) 1) => estRisk k ρ M n R p) p₁ hp₁
  -- real lower bound for the average risk
  have hmin : ∀ b, min (P₀ b) (P₁ b) * (2 * δ) ≤ P₀ b * x₀ b + P₁ b * x₁ b := by
    intro b
    have htri : 2 * δ ≤ x₀ b + x₁ b := by
      refine hsep.trans ?_
      have := abs_sub_le r₀ (R (sampleVec M b)) r₁
      simp only [hx₀, hx₁]; rw [abs_sub_comm (R (sampleVec M b)) r₀]; linarith
    have h0 := sampleProb_nonneg p₀ hp₀ b
    have h1 := sampleProb_nonneg p₁ hp₁ b
    have hx0 : 0 ≤ x₀ b := abs_nonneg _
    have hx1 : 0 ≤ x₁ b := abs_nonneg _
    have hm0 : min (P₀ b) (P₁ b) ≤ P₀ b := min_le_left _ _
    have hm1 : min (P₀ b) (P₁ b) ≤ P₁ b := min_le_right _ _
    have hm : 0 ≤ min (P₀ b) (P₁ b) := le_min h0 h1
    nlinarith [mul_le_mul_of_nonneg_right hm0 hx0, mul_le_mul_of_nonneg_right hm1 hx1,
      mul_le_mul_of_nonneg_left htri hm]
  have hsummin : ∑ b, min (P₀ b) (P₁ b) = 1 - tvDist n p₀ p₁ := by
    have e : ∀ b, min (P₀ b) (P₁ b) = (P₀ b + P₁ b - |P₀ b - P₁ b|) / 2 := by
      intro b; rcases le_total (P₀ b) (P₁ b) with h | h
      · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
    simp_rw [e]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp only [hP₀, hP₁, sampleProb_sum, tvDist]
    ring
  have hTV : 0 ≤ 1 - tvDist n p₀ p₁ := by
    rw [← hsummin]; exact Finset.sum_nonneg (fun b _ => le_min (sampleProb_nonneg p₀ hp₀ b)
      (sampleProb_nonneg p₁ hp₁ b))
  have hreal : δ * (1 - tvDist n p₀ p₁) ≤
      (∑ b, P₀ b * x₀ b) + ∑ b, P₁ b * x₁ b := by
    rw [← Finset.sum_add_distrib]
    calc δ * (1 - tvDist n p₀ p₁) ≤ 2 * δ * (1 - tvDist n p₀ p₁) := by nlinarith
      _ = ∑ b, min (P₀ b) (P₁ b) * (2 * δ) := by rw [← Finset.sum_mul, hsummin]; ring
      _ ≤ _ := Finset.sum_le_sum (fun b _ => hmin b)
  -- 2 * target ≤ E₀ + E₁ ≤ 2 * sup
  have hS0 : 0 ≤ ∑ b, P₀ b * x₀ b :=
    Finset.sum_nonneg (fun b _ => mul_nonneg (sampleProb_nonneg p₀ hp₀ b) (abs_nonneg _))
  have hS1 : 0 ≤ ∑ b, P₁ b * x₁ b :=
    Finset.sum_nonneg (fun b _ => mul_nonneg (sampleProb_nonneg p₁ hp₁ b) (abs_nonneg _))
  have key : 2 * ENNReal.ofReal (δ / 2 * (1 - tvDist n p₀ p₁))
      ≤ 2 * ⨆ p ∈ Set.Icc (0 : ℝ) 1, estRisk k ρ M n R p := by
    calc 2 * ENNReal.ofReal (δ / 2 * (1 - tvDist n p₀ p₁))
        = ENNReal.ofReal (δ * (1 - tvDist n p₀ p₁)) := by
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
      _ ≤ ENNReal.ofReal ((∑ b, P₀ b * x₀ b) + ∑ b, P₁ b * x₁ b) := ENNReal.ofReal_le_ofReal hreal
      _ = estRisk k ρ M n R p₀ + estRisk k ρ M n R p₁ := by
          rw [hE0, hE1, ENNReal.ofReal_add hS0 hS1]
      _ ≤ _ := by rw [two_mul]; exact add_le_add hsup0 hsup1
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp key


open Real Set

/-- the binary divergence as a function of the second argument -/
noncomputable def binKL (a b : ℝ) : ℝ := a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b))

lemma binKL_deriv (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    HasDerivAt (fun x => binKL a x - 2 * (a - x) ^ 2)
      ((b - a) * (1 / (b * (1 - b)) - 4)) b := by
  set g : ℝ → ℝ := fun x => a * Real.log a - a * Real.log x + (1 - a) * Real.log (1 - a)
    - (1 - a) * Real.log (1 - x) - 2 * (a - x) ^ 2 with hg
  have hlog1 : HasDerivAt (fun x => Real.log (1 - x)) (-1 / (1 - b)) b := by
    have hd : HasDerivAt (fun x => 1 - x) (-1) b := by simpa using (hasDerivAt_id b).const_sub 1
    have := hd.log (by linarith)
    simpa using this
  have hsq : HasDerivAt (fun x => 2 * (a - x) ^ 2) (2 * (2 * (a - b) * (-1))) b := by
    have hd : HasDerivAt (fun x => a - x) (-1) b := by simpa using (hasDerivAt_id b).const_sub a
    have := (hd.pow 2).const_mul 2
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  have hgd : HasDerivAt g (-(a * b⁻¹) - (1 - a) * (-1 / (1 - b)) - 2 * (2 * (a - b) * (-1))) b := by
    have := ((((hasDerivAt_const b (a * Real.log a)).sub ((Real.hasDerivAt_log hb0.ne').const_mul a)).add
      (hasDerivAt_const b ((1 - a) * Real.log (1 - a)))).sub (hlog1.const_mul (1 - a))).sub hsq
    refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)).congr_deriv (by ring)
    simp [hg]
  have hev : (fun x => binKL a x - 2 * (a - x) ^ 2) =ᶠ[nhds b] g := by
    filter_upwards [Ioo_mem_nhds hb0 hb1] with x hx
    simp only [binKL, hg]
    rw [Real.log_div ha0.ne' hx.1.ne', Real.log_div (by linarith) (by linarith [hx.2])]; ring
  refine (hgd.congr_of_eventuallyEq hev).congr_deriv ?_
  have : (1 - b) ≠ 0 := by linarith
  have : b ≠ 0 := hb0.ne'
  field_simp; ring

/-- binary Pinsker: `kl(a,b) ≥ 2 (a-b)²` on the open square -/
theorem binary_pinsker (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    2 * (a - b) ^ 2 ≤ binKL a b := by
  set f := fun x => binKL a x - 2 * (a - x) ^ 2 with hf
  have hfa : f a = 0 := by simp [hf, binKL, div_self ha0.ne', div_self (by linarith : (1:ℝ) - a ≠ 0)]
  have hfac : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ 1 / (x * (1 - x)) - 4 := by
    intro x hx
    have hp : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
    rw [sub_nonneg, le_div_iff₀ hp]; nlinarith [sq_nonneg (x - 1 / 2)]
  have hcont : ∀ c d, 0 < c → d < 1 → ContinuousOn f (Icc c d) := by
    intro c d hc hd x hx
    exact (binKL_deriv a x ha0 ha1 (by linarith [hx.1]) (by linarith [hx.2])).continuousAt.continuousWithinAt
  rcases le_total a b with hab | hba
  · -- f increases on [a, b]
    have hmono : MonotoneOn f (Icc a b) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (hcont a b ha0 hb1)
      · intro x hx; rw [interior_Icc] at hx
        exact (binKL_deriv a x ha0 ha1 (by linarith [hx.1]) (by linarith [hx.2])).differentiableAt.differentiableWithinAt
      · intro x hx; rw [interior_Icc] at hx
        rw [(binKL_deriv a x ha0 ha1 (by linarith [hx.1]) (by linarith [hx.2])).deriv]
        exact mul_nonneg (by linarith [hx.1]) (hfac x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    have := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
    simp only [hf] at this hfa; linarith
  · -- f decreases on [b, a]
    have hanti : AntitoneOn f (Icc b a) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc b a) (hcont b a hb0 ha1)
      · intro x hx; rw [interior_Icc] at hx
        exact (binKL_deriv a x ha0 ha1 (by linarith [hx.1]) (by linarith [hx.2])).differentiableAt.differentiableWithinAt
      · intro x hx; rw [interior_Icc] at hx
        rw [(binKL_deriv a x ha0 ha1 (by linarith [hx.1]) (by linarith [hx.2])).deriv]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hx.2]) (hfac x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    have := hanti ⟨le_rfl, hba⟩ ⟨hba, le_rfl⟩ hba
    simp only [hf] at this hfa; linarith

/-- binary Pinsker on the closed range of the first argument -/
theorem binary_pinsker' (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b < 1) :
    2 * (a - b) ^ 2 ≤ binKL a b := by
  -- `a ↦ binKL a b - 2 (a - b)^2` is continuous on ℝ
  have hc : Continuous (fun x : ℝ => binKL x b - 2 * (x - b) ^ 2) := by
    have e : (fun x : ℝ => binKL x b) = fun x => (x * Real.log x - x * Real.log b)
        + ((1 - x) * Real.log (1 - x) - (1 - x) * Real.log (1 - b)) := by
      funext x
      simp only [binKL]
      rcases eq_or_ne x 0 with h0 | h0
      · subst h0; simp
      rcases eq_or_ne (1 - x) 0 with h1 | h1
      · rw [h1]; simp [Real.log_div h0 hb0.ne']; ring
      rw [Real.log_div h0 hb0.ne', Real.log_div h1 (by linarith)]; ring
    rw [show (fun x : ℝ => binKL x b - 2 * (x - b) ^ 2)
        = fun x => ((x * Real.log x - x * Real.log b)
          + ((1 - x) * Real.log (1 - x) - (1 - x) * Real.log (1 - b))) - 2 * (x - b) ^ 2 from by
        funext x; rw [show binKL x b = _ from congrFun e x]]
    have h1 := Real.continuous_mul_log
    have h2 : Continuous (fun x : ℝ => (1 - x) * Real.log (1 - x)) :=
      h1.comp (continuous_const.sub continuous_id)
    fun_prop
  -- the interior points are dense near the endpoints
  have hclosed : IsClosed {x : ℝ | 0 ≤ binKL x b - 2 * (x - b) ^ 2} :=
    isClosed_le continuous_const hc
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ {x : ℝ | 0 ≤ binKL x b - 2 * (x - b) ^ 2} := by
    intro x hx
    have := binary_pinsker x b hx.1 hx.2 hb0 hb1
    simp only [Set.mem_setOf_eq]; nlinarith [sq_nonneg (x - b), sq_nonneg (b - x)]
  have hcl := hclosed.closure_subset_iff.mpr hsub
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hcl
  have := hcl ⟨ha0, ha1⟩
  simp only [Set.mem_setOf_eq] at this
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - a)]


open Finset Real

/-- Cover–Thomas Theorem 2.7.1 (log-sum inequality), for `a ≥ 0`, `b > 0`. -/
theorem log_sum_ineq {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, 0 < b i) (hs : s.Nonempty) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) ≤ ∑ i ∈ s, a i * Real.log (a i / b i) := by
  set B := ∑ i ∈ s, b i with hB
  have hB0 : 0 < B := Finset.sum_pos hb hs
  -- Jensen for φ(x) = x log x with weights b_i / B at points a_i / b_i
  have hJ := convexOn_mul_log.map_sum_le (t := s) (w := fun i => b i / B) (p := fun i => a i / b i)
    (fun i hi => (div_pos (hb i hi) hB0).le) (by rw [← Finset.sum_div, div_self hB0.ne'])
    (fun i hi => Set.mem_Ici.mpr (div_nonneg (ha i hi) (hb i hi).le))
  have e1 : ∑ i ∈ s, (b i / B) • (a i / b i) = (∑ i ∈ s, a i) / B := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun i hi => ?_)
    have := (hb i hi).ne'; rw [smul_eq_mul]; field_simp
  have e2 : ∑ i ∈ s, (b i / B) • ((a i / b i) * Real.log (a i / b i))
      = (∑ i ∈ s, a i * Real.log (a i / b i)) / B := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun i hi => ?_)
    have := (hb i hi).ne'; rw [smul_eq_mul]; field_simp
  rw [e1, e2] at hJ
  have := mul_le_mul_of_nonneg_left hJ hB0.le
  rw [mul_div_cancel₀ _ hB0.ne'] at this
  calc (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / B)
      = B * ((∑ i ∈ s, a i) / B * Real.log ((∑ i ∈ s, a i) / B)) := by field_simp
    _ ≤ _ := this


/-- finite Pinsker: `½ (Σ |P - Q|)² ≤ Σ P log (P / Q)` for distributions with `Q > 0` -/
theorem finite_pinsker {ι : Type*} [Fintype ι] (P Q : ι → ℝ) (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i)
    (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i = 1) :
    (1 / 2) * (∑ i, |P i - Q i|) ^ 2 ≤ ∑ i, P i * Real.log (P i / Q i) := by
  classical
  have hne : (Finset.univ : Finset ι).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hQ1; norm_num at hQ1
  set A := Finset.univ.filter (fun i => Q i < P i) with hA
  set Ac := Finset.univ.filter (fun i => ¬ Q i < P i) with hAc
  set a := ∑ i ∈ A, P i
  set b := ∑ i ∈ A, Q i
  have hsplitP : ∑ i ∈ A, P i + ∑ i ∈ Ac, P i = 1 := by rw [← hP1, Finset.sum_filter_add_sum_filter_not]
  have hsplitQ : ∑ i ∈ A, Q i + ∑ i ∈ Ac, Q i = 1 := by rw [← hQ1, Finset.sum_filter_add_sum_filter_not]
  have hsplitK : ∑ i ∈ A, P i * Real.log (P i / Q i) + ∑ i ∈ Ac, P i * Real.log (P i / Q i)
      = ∑ i, P i * Real.log (P i / Q i) := Finset.sum_filter_add_sum_filter_not _ _ _
  -- L1 distance = 2 (a - b)
  have hL1 : ∑ i, |P i - Q i| = 2 * (a - b) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => Q i < P i)]
    have h1 : ∑ i ∈ A, |P i - Q i| = a - b := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i hi => abs_of_pos (by have := (Finset.mem_filter.mp hi).2; linarith))
    have h2 : ∑ i ∈ Ac, |P i - Q i| = (∑ i ∈ Ac, Q i) - ∑ i ∈ Ac, P i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i hi => by
        have := (Finset.mem_filter.mp hi).2; rw [abs_of_nonpos (by linarith)]; ring)
    rw [← hA, ← hAc, h1, h2]; linarith
  -- RHS ≥ 0 (Gibbs) for the degenerate cases
  have hgibbs : 0 ≤ ∑ i, P i * Real.log (P i / Q i) := by
    have := log_sum_ineq Finset.univ P Q (fun i _ => hP i) (fun i _ => hQ i) hne
    rw [hP1, hQ1, div_one, Real.log_one, mul_zero] at this; exact this
  by_cases hAe : A.Nonempty
  · by_cases hAce : Ac.Nonempty
    · have hb0 : 0 < b := Finset.sum_pos (fun i _ => hQ i) hAe
      have hb1 : b < 1 := by
        have : 0 < ∑ i ∈ Ac, Q i := Finset.sum_pos (fun i _ => hQ i) hAce
        linarith
      have ha0 : 0 ≤ a := Finset.sum_nonneg (fun i _ => hP i)
      have ha1 : a ≤ 1 := by
        have : 0 ≤ ∑ i ∈ Ac, P i := Finset.sum_nonneg (fun i _ => hP i)
        linarith
      have hls1 := log_sum_ineq A P Q (fun i _ => hP i) (fun i _ => hQ i) hAe
      have hls2 := log_sum_ineq Ac P Q (fun i _ => hP i) (fun i _ => hQ i) hAce
      have hPc : ∑ i ∈ Ac, P i = 1 - a := by linarith
      have hQc : ∑ i ∈ Ac, Q i = 1 - b := by linarith
      rw [hPc, hQc] at hls2
      have hbin := binary_pinsker' a b ha0 ha1 hb0 hb1
      unfold binKL at hbin
      rw [hL1]
      nlinarith
    · -- Ac empty: P > Q everywhere, impossible with equal sums
      exfalso
      rw [Finset.not_nonempty_iff_eq_empty] at hAce
      have hlt : ∑ i, Q i < ∑ i, P i := by
        apply Finset.sum_lt_sum_of_nonempty hne
        intro i _
        by_contra h
        have : i ∈ Ac := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
        rw [hAce] at this; simp at this
      linarith
  · -- A empty: P ≤ Q, equal sums force a = b = 0
    rw [Finset.not_nonempty_iff_eq_empty] at hAe
    have : a = 0 ∧ b = 0 := by simp [a, b, hAe]
    rw [hL1, this.1, this.2]; simpa using hgibbs


open UniformDRO.LowerBound

theorem pinskerDisp (n : ℕ) (p₁ p₂ : ℝ) (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Icc (0 : ℝ) 1) :
    tvDist n p₁ p₂ ^ 2 ≤ n / 2 * BanditAlgorithm.bernoulliRelativeEntropy p₂ p₁ := by
  classical
  obtain ⟨h10, h11⟩ := hp₁
  obtain ⟨h20, h21⟩ := hp₂
  set w : ℝ → Bool → ℝ := fun p x => if x then p else 1 - p with hw
  have hSP : ∀ p (b : Fin n → Bool), sampleProb p b = ∏ i, w p (b i) := fun p b => rfl
  have hsum : ∀ p, ∑ b : Fin n → Bool, sampleProb p b = 1 := by
    intro p; simp only [hSP]
    rw [← Fintype.prod_sum (fun (_ : Fin n) (x : Bool) => w p x)]; simp [hw]
  have hw1 : ∀ x, 0 < w p₁ x := fun x => by cases x <;> simp [hw] <;> linarith
  have hw2 : ∀ x, 0 ≤ w p₂ x := fun x => by cases x <;> simp [hw] <;> linarith
  set h : Bool → ℝ := fun x => Real.log (w p₂ x / w p₁ x) with hh
  -- tensorization of the divergence
  have hpt : ∀ b : Fin n → Bool, sampleProb p₂ b * Real.log (sampleProb p₂ b / sampleProb p₁ b)
      = sampleProb p₂ b * ∑ i, h (b i) := by
    intro b
    by_cases h0 : sampleProb p₂ b = 0
    · rw [h0, zero_mul, zero_mul]
    · congr 1
      have hpos : ∀ i, w p₂ (b i) ≠ 0 := by
        intro i hi; apply h0; rw [hSP]; exact Finset.prod_eq_zero (Finset.mem_univ i) hi
      rw [hSP, hSP, ← Finset.prod_div_distrib, Real.log_prod]
      intro i _; exact div_ne_zero (hpos i) (hw1 _).ne'
  have hmarg : ∀ i : Fin n, ∑ b : Fin n → Bool, sampleProb p₂ b * h (b i)
      = BanditAlgorithm.bernoulliRelativeEntropy p₂ p₁ := by
    intro i
    have e : ∀ b : Fin n → Bool, sampleProb p₂ b * h (b i)
        = ∏ j, (fun (j : Fin n) (x : Bool) => w p₂ x * (if j = i then h x else 1)) j (b j) := by
      intro b
      rw [hSP, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i]; simp
    simp_rw [e]
    rw [← Fintype.prod_sum (fun (j : Fin n) (x : Bool) => w p₂ x * (if j = i then h x else 1))]
    rw [Finset.prod_eq_single i]
    · simp [hw, hh, BanditAlgorithm.bernoulliRelativeEntropy]
    · intro j _ hj; simp [hj, hw]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hKL : ∑ b : Fin n → Bool, sampleProb p₂ b * Real.log (sampleProb p₂ b / sampleProb p₁ b)
      = n * BanditAlgorithm.bernoulliRelativeEntropy p₂ p₁ := by
    simp_rw [hpt, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [hmarg]; simp
  -- finite Pinsker
  have hP := finite_pinsker (fun b => sampleProb p₂ b) (fun b => sampleProb p₁ b)
    (fun b => by rw [hSP]; exact Finset.prod_nonneg (fun i _ => hw2 _))
    (fun b => by rw [hSP]; exact Finset.prod_pos (fun i _ => hw1 _)) (hsum p₂) (hsum p₁)
  rw [hKL] at hP
  have hTV : tvDist n p₁ p₂ = (1 / 2) * ∑ b : Fin n → Bool, |sampleProb p₂ b - sampleProb p₁ b| := by
    unfold tvDist; congr 1; refine Finset.sum_congr rfl (fun b _ => abs_sub_comm _ _)
  rw [hTV]
  nlinarith [hP]


open Real

/-- binary KL ≤ χ²: `d(r, p) ≤ (r - p)² / (p (1 - p))` for `r ∈ [0,1]`, `p ∈ (0,1)` -/
theorem binKL_le_chi2 (r p : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hp0 : 0 < p) (hp1 : p < 1) :
    r * Real.log (r / p) + (1 - r) * Real.log ((1 - r) / (1 - p)) ≤ (r - p) ^ 2 / (p * (1 - p)) := by
  have h1p : 0 < 1 - p := by linarith
  -- termwise `x log (x / y) ≤ x (x / y - 1)`
  have key : ∀ x y : ℝ, 0 ≤ x → 0 < y → x * Real.log (x / y) ≤ x * (x / y - 1) := by
    intro x y hx hy
    rcases hx.eq_or_lt with h | h
    · rw [← h]; simp
    · exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos h hy)) hx
  have k1 := key r p hr0 hp0
  have k2 := key (1 - r) (1 - p) (by linarith) h1p
  have e : r * (r / p - 1) + (1 - r) * ((1 - r) / (1 - p) - 1) = (r - p) ^ 2 / (p * (1 - p)) := by
    field_simp; ring
  linarith

/-- concavity of `x ↦ (1 - x)^a` for `a ∈ (0,1]`: `1 - (1 - x)^a ≥ a x` -/
theorem one_sub_rpow_ge (a x : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    a * x ≤ 1 - (1 - x) ^ a := by
  -- Bernoulli: (1 + t)^a ≤ 1 + a t for t ≥ -1, 0 ≤ a ≤ 1
  have := rpow_one_add_le_one_add_mul_self (show (-1 : ℝ) ≤ -x by linarith) ha0.le ha1
  have e : (1 : ℝ) + -x = 1 - x := by ring
  rw [e] at this
  linarith

lemma value_le_z1 (k ρ z₀ z₁ p : ℝ) (hz : z₀ ≤ z₁) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    BddAbove {v : ℝ | ∃ L : ℝ → ℝ, Measurable L ∧ (∀ x, 0 ≤ L x) ∧ Integrable L (twoPointLaw z₀ z₁ p) ∧
      ∫ x, L x ∂(twoPointLaw z₀ z₁ p) = 1 ∧ Integrable (fun x => L x * id x) (twoPointLaw z₀ z₁ p) ∧
      ∫⁻ x, ENNReal.ofReal (UniformDRO.Concentration.cressieRead k (L x)) ∂(twoPointLaw z₀ z₁ p)
        ≤ ENNReal.ofReal ρ ∧
      v = ∫ x, L x * id x ∂(twoPointLaw z₀ z₁ p)} := by
  refine ⟨z₁, ?_⟩
  rintro v ⟨L, -, hLnn, -, hL1, -, -, rfl⟩
  rw [(tp_integral z₀ z₁ p hp0 hp1 _).2] at hL1 ⊢
  simp only [id]
  have h1p : 0 ≤ 1 - p := by linarith
  have h := congrArg (fun t => t * z₁) hL1
  nlinarith [mul_nonneg (mul_nonneg h1p (hLnn z₀)) (sub_nonneg.mpr hz)]


theorem r12c (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (z₀ z₁ p : ℝ) (hz : z₀ ≤ z₁)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hp1 : p ≤ pk k ρ)
    (hp2 : p ≤ 1 - (1 - β) ^ (1 - UniformDRO.Concentration.kstar k) * pk k ρ) :
    β ^ (1 / k) * UniformDRO.Concentration.ck k ρ * p ^ (1 / UniformDRO.Concentration.kstar k) * z₁ +
        (1 - β ^ (1 / k) * UniformDRO.Concentration.ck k ρ * p ^ (1 / UniformDRO.Concentration.kstar k)) * z₀ ≤
      UniformDRO.Concentration.robustRisk k ρ (twoPointLaw z₀ z₁ p) id := by
  classical
  obtain ⟨hp0, hp1'⟩ := hp
  obtain ⟨hβ0, hβ1⟩ := hβ
  set c := 1 + k * (k - 1) * ρ with hc
  have hc0 : 0 < c := by
    have : 0 < k * (k - 1) * ρ := mul_pos (mul_pos (by linarith) (by linarith)) hρ
    linarith
  have hk0 : 0 < k := by linarith
  have hk1 : 0 < k - 1 := by linarith
  have hck : UniformDRO.Concentration.ck k ρ = c ^ (1 / k) := rfl
  have hks : 1 / UniformDRO.Concentration.kstar k = 1 - 1 / k := by
    unfold UniformDRO.Concentration.kstar; field_simp
  have hks2 : 1 - UniformDRO.Concentration.kstar k = -(1 / (k - 1)) := by
    unfold UniformDRO.Concentration.kstar; field_simp; ring
  have hpk : pk k ρ = c ^ (-(1 / (k - 1))) := rfl
  rw [hck, hks]
  rw [hks2, hpk] at hp2
  rw [hpk] at hp1
  set A := β ^ (1 / k) * c ^ (1 / k) * p ^ (1 - 1 / k) with hA
  have goal_form : A * z₁ + (1 - A) * z₀ = z₀ + A * (z₁ - z₀) := by ring
  rw [goal_form]
  unfold UniformDRO.Concentration.robustRisk
  rcases hp0.eq_or_lt with h0 | hpos
  · -- p = 0: the trivial ratio
    subst h0
    have hA0 : A = 0 := by
      rw [hA, Real.zero_rpow (by
        have : 1 / k < 1 := by rw [div_lt_one hk0]; linarith
        linarith), mul_zero]
    rw [hA0, zero_mul, add_zero]
    refine le_csSup (value_le_z1 k ρ z₀ z₁ 0 hz le_rfl (by norm_num))
      ⟨fun _ => 1, measurable_const, fun _ => zero_le_one, (tp_integral z₀ z₁ 0 le_rfl (by norm_num) _).1,
        ?_, (tp_integral z₀ z₁ 0 le_rfl (by norm_num) _).1, ?_, ?_⟩
    · rw [(tp_integral z₀ z₁ 0 le_rfl (by norm_num) _).2]; ring
    · rw [tp_lintegral]; simp [UniformDRO.Concentration.cressieRead]
    · rw [(tp_integral z₀ z₁ 0 le_rfl (by norm_num) _).2]; simp
  -- p > 0
  have hq0 : 0 < (1 - β) ^ (-(1 / (k - 1))) * c ^ (-(1 / (k - 1))) := by positivity
  have hp_lt1 : p < 1 := by linarith
  have h1p : 0 < 1 - p := by linarith
  set L1 := β ^ (1 / k) * c ^ (1 / k) * p ^ (-(1 / k)) with hL1def
  have hpL1 : p * L1 = A := by
    rw [hL1def, hA]
    have : p * p ^ (-(1 / k)) = p ^ (1 - 1 / k) := by
      rw [← Real.rpow_one_add' hpos.le (by
        have : 1 / k < 1 := by rw [div_lt_one hk0]; linarith
        linarith)]; congr 1
    rw [← this]; ring
  -- p L1 < 1
  have hA1 : A ≤ β ^ (1 / k) := by
    have hpp : p ^ (1 - 1 / k) ≤ (c ^ (-(1 / (k - 1)))) ^ (1 - 1 / k) :=
      Real.rpow_le_rpow hpos.le hp1 (by
        have : 1 / k < 1 := by rw [div_lt_one hk0]; linarith
        linarith)
    have hpow : (c ^ (-(1 / (k - 1)))) ^ (1 - 1 / k) = c ^ (-(1 / k)) := by
      rw [← Real.rpow_mul hc0.le]; congr 1; field_simp
    rw [hpow] at hpp
    calc A = β ^ (1 / k) * (c ^ (1 / k) * p ^ (1 - 1 / k)) := by rw [hA]; ring
      _ ≤ β ^ (1 / k) * (c ^ (1 / k) * c ^ (-(1 / k))) := by gcongr
      _ = β ^ (1 / k) := by rw [← Real.rpow_add hc0]; simp
  have hβk : β ^ (1 / k) < 1 := Real.rpow_lt_one hβ0.le hβ1 (by positivity)
  set L0 := (1 - A) / (1 - p) with hL0def
  have hL0nn : 0 ≤ L0 := div_nonneg (by linarith) h1p.le
  have hL1nn : 0 ≤ L1 := by positivity
  set L : ℝ → ℝ := fun x => if x = z₁ then L1 else L0 with hL
  by_cases hzz : z₀ = z₁
  · -- degenerate support: every feasible value equals z₀ = z₁
    subst hzz
    have hv : z₀ + A * (z₀ - z₀) = ∫ x, (fun _ => (1 : ℝ)) x * id x ∂(twoPointLaw z₀ z₀ p) := by
      rw [(tp_integral z₀ z₀ p hp0 hp1' _).2]; simp; ring
    rw [hv]
    refine le_csSup (value_le_z1 k ρ z₀ z₀ p le_rfl hp0 hp1')
      ⟨fun _ => 1, measurable_const, fun _ => zero_le_one, (tp_integral z₀ z₀ p hp0 hp1' _).1,
        ?_, (tp_integral z₀ z₀ p hp0 hp1' _).1, ?_, rfl⟩
    · rw [(tp_integral z₀ z₀ p hp0 hp1' _).2]; ring
    · rw [tp_lintegral]; simp [UniformDRO.Concentration.cressieRead]
  have hLz0 : L z₀ = L0 := by simp [hL, hzz]
  have hLz1 : L z₁ = L1 := by simp [hL]
  have hLm : Measurable L := Measurable.ite (measurableSet_singleton z₁) measurable_const measurable_const
  have hLnn : ∀ x, 0 ≤ L x := fun x => by simp only [hL]; split_ifs <;> assumption
  refine le_of_eq_of_le ?_ (le_csSup (value_le_z1 k ρ z₀ z₁ p hz hp0 hp1')
    ⟨L, hLm, hLnn, (tp_integral z₀ z₁ p hp0 hp1' _).1, ?_, (tp_integral z₀ z₁ p hp0 hp1' _).1, ?_, rfl⟩)
  · rw [(tp_integral z₀ z₁ p hp0 hp1' _).2, hLz0, hLz1]; simp only [id]
    have e0 : (1 - p) * L0 = 1 - A := by rw [hL0def]; field_simp
    calc z₀ + A * (z₁ - z₀) = (1 - A) * z₀ + A * z₁ := by ring
      _ = ((1 - p) * L0) * z₀ + (p * L1) * z₁ := by rw [e0, hpL1]
      _ = _ := by ring
  · rw [(tp_integral z₀ z₁ p hp0 hp1' _).2, hLz0, hLz1]
    have e0 : (1 - p) * L0 = 1 - A := by rw [hL0def]; field_simp
    linarith [hpL1]
  · -- divergence constraint
    rw [tp_lintegral, hLz0, hLz1]
    have hf0 := cr_nonneg k L0 hk hL0nn
    have hf1 := cr_nonneg k L1 hk hL1nn
    rw [← ENNReal.ofReal_mul h1p.le, ← ENNReal.ofReal_mul hp0,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold UniformDRO.Concentration.cressieRead
    have hkk : 0 < k * (k - 1) := by nlinarith
    -- p L1^k = β c
    have hpL1k : p * L1 ^ k = β * c := by
      rw [hL1def, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul hβ0.le, ← Real.rpow_mul hc0.le, ← Real.rpow_mul hpos.le]
      have e1 : 1 / k * k = 1 := by field_simp
      have e2 : -(1 / k) * k = -1 := by field_simp
      rw [e1, e2, Real.rpow_one, Real.rpow_one, Real.rpow_neg_one]
      field_simp
    -- (1 - p) L0^k ≤ (1 - β) c
    have hL0le : L0 ≤ 1 / (1 - p) := by
      rw [hL0def]; exact div_le_div_of_nonneg_right (by nlinarith [show 0 ≤ A by positivity]) h1p.le
    have hL0k : (1 - p) * L0 ^ k ≤ (1 - β) * c := by
      have h1 : L0 ^ k ≤ (1 / (1 - p)) ^ k := Real.rpow_le_rpow hL0nn hL0le hk0.le
      have h2 : (1 - p) * (1 / (1 - p)) ^ k = (1 - p) ^ (1 - k) := by
        rw [one_div, Real.inv_rpow h1p.le, Real.rpow_sub h1p, Real.rpow_one, div_eq_mul_inv]
      have h3 : (1 - p) ^ (1 - k) ≤ (1 - β) * c := by
        -- from hp2: 1 - p ≥ ((1-β) c)^(-1/(k-1))
        have hq : ((1 - β) * c) ^ (-(1 / (k - 1))) ≤ 1 - p := by
          rw [Real.mul_rpow (by linarith) hc0.le]; linarith
        have hqpos : 0 < ((1 - β) * c) ^ (-(1 / (k - 1))) := by
          have : 0 < (1 - β) * c := mul_pos (by linarith) hc0
          positivity
        have := Real.rpow_le_rpow_of_nonpos hqpos hq (by linarith : 1 - k ≤ 0)
        rw [← Real.rpow_mul (by have : 0 < (1 - β) * c := mul_pos (by linarith) hc0; linarith)] at this
        have e : -(1 / (k - 1)) * (1 - k) = 1 := by field_simp; ring
        rw [e, Real.rpow_one] at this
        exact this
      calc (1 - p) * L0 ^ k ≤ (1 - p) * (1 / (1 - p)) ^ k := by gcongr
        _ = (1 - p) ^ (1 - k) := h2
        _ ≤ _ := h3
    have e0 : (1 - p) * L0 = 1 - A := by rw [hL0def]; field_simp
    have hEL : (1 - p) * L0 + p * L1 = 1 := by linarith [hpL1]
    clear_value L L0 L1 A
    have e : (1 - p) * ((L0 ^ k - k * L0 + k - 1) / (k * (k - 1)))
        + p * ((L1 ^ k - k * L1 + k - 1) / (k * (k - 1)))
        = ((1 - p) * L0 ^ k + p * L1 ^ k - k * ((1 - p) * L0 + p * L1) + (k - 1)) / (k * (k - 1)) := by
      ring
    rw [e, hEL, hpL1k, div_le_iff₀ hkk]
    have hcc : c - 1 = k * (k - 1) * ρ := by rw [hc]; ring
    linarith [hL0k, hcc]


open UniformDRO.LowerBound in
/-- Theorem 3, first regime (Le Cam with `p₀ = p_k`, `p₁ = p_k - Δ`). -/
theorem theorem3_branch1 (k ρ M : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (hM : 0 < M) (n : ℕ) (hn : 0 < n) :
    ENNReal.ofReal (M * (1 / (8 * UniformDRO.Concentration.kstar k * pk k ρ) *
        min (min (Real.sqrt (pk k ρ * (1 - pk k ρ) / (16 * n))) ((1 - pk k ρ) / 2)) (pk k ρ)))
      ≤ minimaxRisk k ρ M n := by
  set c := 1 + k * (k - 1) * ρ with hc
  have hc1 : 1 < c := by
    have : 0 < k * (k - 1) * ρ := mul_pos (mul_pos (by linarith) (by linarith)) hρ; linarith
  have hc0 : 0 < c := by linarith
  have hk1 : 0 < k - 1 := by linarith
  have hk0 : 0 < k := by linarith
  set P := pk k ρ with hP
  have hPdef : P = c ^ (-(1 / (k - 1))) := rfl
  have hP0 : 0 < P := by rw [hPdef]; positivity
  have hP1 : P < 1 := by
    rw [hPdef]; exact Real.rpow_lt_one_of_one_lt_of_neg hc1 (by have := div_pos one_pos hk1; linarith)
  set a := 1 / UniformDRO.Concentration.kstar k with ha
  have ha_eq : a = (k - 1) / k := by rw [ha]; unfold UniformDRO.Concentration.kstar; field_simp
  have ha0 : 0 < a := by rw [ha_eq]; positivity
  have ha1 : a ≤ 1 := by rw [ha_eq, div_le_one hk0]; linarith
  set Δ := min (min (Real.sqrt (P * (1 - P) / (16 * n))) ((1 - P) / 2)) P with hΔ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hΔ0 : 0 < Δ := by
    rw [hΔ]; refine lt_min (lt_min (Real.sqrt_pos.mpr (by have := mul_pos hP0 (by linarith : (0:ℝ) < 1 - P); positivity)) (by linarith)) hP0
  have hΔP : Δ ≤ P := min_le_right _ _
  have hΔsq : Δ ≤ Real.sqrt (P * (1 - P) / (16 * n)) := (min_le_left _ _).trans (min_le_left _ _)
  set p₁ := P - Δ with hp₁
  have hp₁0 : 0 ≤ p₁ := by linarith
  have hp₁1 : p₁ ≤ 1 := by linarith
  -- robust risks
  have hr0 := r12a k ρ hk hρ 0 M P hM.le ⟨hP0.le, hP1.le⟩ le_rfl
  have hr1 := r12b k ρ hk hρ 0 M p₁ hM.le ⟨hp₁0, hp₁1⟩ (by linarith)
  have hcP : UniformDRO.Concentration.ck k ρ * P ^ a = 1 := by
    show c ^ (1 / k) * (c ^ (-(1 / (k - 1)))) ^ a = 1
    rw [← Real.rpow_mul hc0.le, ← Real.rpow_add hc0, ha_eq]
    have : 1 / k + -(1 / (k - 1)) * ((k - 1) / k) = 0 := by field_simp; ring
    rw [this, Real.rpow_zero]
  have hp₁a : p₁ ^ a = P ^ a * (1 - Δ / P) ^ a := by
    rw [← Real.mul_rpow hP0.le (by have := div_le_one hP0 |>.mpr hΔP; linarith)]
    congr 1; rw [hp₁]; field_simp
  have hsepR : M * a * (Δ / P) ≤
      UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M P) id -
        UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M p₁) id := by
    rw [hr0]
    have hb := one_sub_rpow_ge a (Δ / P) ha0 ha1 (by positivity) ((div_le_one hP0).mpr hΔP)
    have : UniformDRO.Concentration.ck k ρ * p₁ ^ a = (1 - Δ / P) ^ a := by
      rw [hp₁a, ← mul_assoc, hcP, one_mul]
    rw [ha] at this hb
    have hr1' : UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M p₁) id ≤ (1 - Δ / P) ^ a * M := by
      rw [ha]; nlinarith [hr1, this]
    rw [ha] at hr1'
    nlinarith [mul_le_mul_of_nonneg_left hb hM.le]
  set δ := M * a * (Δ / P) / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hsep : 2 * δ ≤ |UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M P) id -
      UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M p₁) id| := by
    rw [hδ]; linarith [le_abs_self (UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M P) id -
      UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M p₁) id)]
  have hLC := leCam k ρ hk hρ M hM n P p₁ δ ⟨hP0.le, hP1.le⟩ ⟨hp₁0, hp₁1⟩ hδ0 hsep
  -- total variation ≤ 1/2
  have hPD := pinskerDisp n P p₁ ⟨hP0, hP1⟩ ⟨hp₁0, hp₁1⟩
  have hchi := binKL_le_chi2 p₁ P hp₁0 hp₁1 hP0 hP1
  have hD : (p₁ - P) ^ 2 = Δ ^ 2 := by rw [hp₁]; ring
  have hΔ2 : Δ ^ 2 ≤ P * (1 - P) / (16 * n) := by
    have := pow_le_pow_left₀ hΔ0.le hΔsq 2
    rwa [Real.sq_sqrt (by have := mul_pos hP0 (by linarith : (0:ℝ) < 1 - P); positivity)] at this
  have hPP : 0 < P * (1 - P) := mul_pos hP0 (by linarith)
  have hTV2 : tvDist n P p₁ ^ 2 ≤ 1 / 32 := by
    unfold BanditAlgorithm.bernoulliRelativeEntropy at hPD
    have h1 : (p₁ - P) ^ 2 / (P * (1 - P)) ≤ 1 / (16 * n) := by
      rw [hD, div_le_iff₀ hPP]; rw [le_div_iff₀ (by positivity)] at hΔ2
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; linarith
    calc tvDist n P p₁ ^ 2 ≤ n / 2 * (p₁ * Real.log (p₁ / P) + (1 - p₁) * Real.log ((1 - p₁) / (1 - P))) := hPD
      _ ≤ n / 2 * (1 / (16 * n)) := by gcongr; exact hchi.trans h1
      _ = 1 / 32 := by field_simp; ring
  have hTV0 : 0 ≤ tvDist n P p₁ := by
    unfold tvDist; exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun b _ => abs_nonneg _))
  have hTV : tvDist n P p₁ ≤ 1 / 2 := by nlinarith
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hLC
  rw [hδ, ha]
  have : M * (1 / UniformDRO.Concentration.kstar k) * (Δ / P) / 2 / 2 * (1 - tvDist n P p₁)
      ≥ M * (1 / UniformDRO.Concentration.kstar k) * (Δ / P) / 8 := by
    have hpos : 0 ≤ M * (1 / UniformDRO.Concentration.kstar k) * (Δ / P) := by rw [← ha]; positivity
    have h12 : (1 : ℝ) / 2 ≤ 1 - tvDist n P p₁ := by linarith
    have := mul_le_mul_of_nonneg_left h12 (by positivity : 0 ≤ M * (1 / UniformDRO.Concentration.kstar k) * (Δ / P) / 2 / 2)
    linarith
  calc M * (1 / (8 * UniformDRO.Concentration.kstar k * P) * Δ)
      = M * (1 / UniformDRO.Concentration.kstar k) * (Δ / P) / 8 := by
        have : UniformDRO.Concentration.kstar k ≠ 0 := by
          unfold UniformDRO.Concentration.kstar; exact (div_pos hk0 hk1).ne'
        field_simp
    _ ≤ _ := this

open UniformDRO.LowerBound in
/-- Theorem 3, second regime (Le Cam with `p₀ = 0`, `p₁ = Δ₂`). -/
theorem theorem3_branch2 (k ρ M : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (hM : 0 < M) (n : ℕ) (hn : 0 < n) :
    ENNReal.ofReal (M * (1 / 8 * βk k ρ ^ (1 / k) * UniformDRO.Concentration.ck k ρ *
          (min (min (1 / (4 * (n : ℝ))) (pk k ρ))
            (1 - (1 - βk k ρ) ^ (1 - UniformDRO.Concentration.kstar k) * pk k ρ)) ^ (1 / UniformDRO.Concentration.kstar k)))
      ≤ minimaxRisk k ρ M n := by
  set c := 1 + k * (k - 1) * ρ with hc
  have hkk : 0 < k * (k - 1) * ρ := mul_pos (mul_pos (by linarith) (by linarith)) hρ
  have hc1 : 1 < c := by linarith
  have hc0 : 0 < c := by linarith
  have hk1 : 0 < k - 1 := by linarith
  have hk0 : 0 < k := by linarith
  set P := pk k ρ with hP
  have hP0 : 0 < P := by show 0 < c ^ (-(1 / (k - 1))); positivity
  set β := βk k ρ with hβ
  have hβ0 : 0 < β := by rw [hβ]; unfold βk; positivity
  have hβ1 : β < 1 := by
    rw [hβ]; unfold βk; rw [div_lt_one (by positivity)]; linarith
  set a := 1 / UniformDRO.Concentration.kstar k with ha
  have ha_eq : a = (k - 1) / k := by rw [ha]; unfold UniformDRO.Concentration.kstar; field_simp
  have ha0 : 0 < a := by rw [ha_eq]; positivity
  set Δ := min (min (1 / (4 * (n : ℝ))) P) (1 - (1 - β) ^ (1 - UniformDRO.Concentration.kstar k) * P) with hΔ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hΔn : Δ ≤ 1 / (4 * n) := (min_le_left _ _).trans (min_le_left _ _)
  have hΔP : Δ ≤ P := (min_le_left _ _).trans (min_le_right _ _)
  have hΔ2 : Δ ≤ 1 - (1 - β) ^ (1 - UniformDRO.Concentration.kstar k) * P := min_le_right _ _
  have hq : 0 < (1 - β) ^ (1 - UniformDRO.Concentration.kstar k) * P := by
    have : 0 < 1 - β := by linarith
    positivity
  have hΔ1 : Δ < 1 := by linarith
  have hΔq : Δ ≤ 1 / 4 := hΔn.trans (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
  have hks : 1 - UniformDRO.Concentration.kstar k = -(1 / (k - 1)) := by
    unfold UniformDRO.Concentration.kstar; field_simp; ring
  have hβc : (1 - β) * c = 1 + k * (k - 1) * ρ / 2 := by
    rw [hβ]; unfold βk; rw [← hc]; field_simp; ring
  have hthird : 0 < 1 - (1 - β) ^ (1 - UniformDRO.Concentration.kstar k) * P := by
    have e : (1 - β) ^ (1 - UniformDRO.Concentration.kstar k) * P = ((1 - β) * c) ^ (-(1 / (k - 1))) := by
      rw [hks, Real.mul_rpow (by linarith) hc0.le]; rfl
    rw [e, sub_pos, hβc]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by have := div_pos one_pos hk1; linarith)
  have hΔ0 : 0 < Δ := by
    rw [hΔ]; exact lt_min (lt_min (by positivity) hP0) hthird
  -- robust risks
  have hr0 := r12b k ρ hk hρ 0 M 0 hM.le ⟨le_rfl, zero_le_one⟩ hP0.le
  rw [Real.zero_rpow ha0.ne', mul_zero, zero_mul, mul_zero, zero_add] at hr0
  have hr1 := r12c k ρ hk hρ 0 M Δ hM.le ⟨hΔ0.le, hΔ1.le⟩ β ⟨hβ0, hβ1⟩ hΔP hΔ2
  rw [mul_zero, add_zero] at hr1
  set S := β ^ (1 / k) * UniformDRO.Concentration.ck k ρ * Δ ^ a * M with hS
  have hsep' : S ≤ UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M Δ) id
      - UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M 0) id := by
    rw [hS, ha]; linarith
  have hS0 : 0 < S := by
    rw [hS]; have : 0 < UniformDRO.Concentration.ck k ρ := by
      show 0 < c ^ (1 / k); positivity
    positivity
  set δ := S / 2 with hδ
  have hsep : 2 * δ ≤ |UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M 0) id -
      UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M Δ) id| := by
    rw [abs_sub_comm, hδ]
    linarith [le_abs_self (UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M Δ) id -
      UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M 0) id)]
  have hLC := leCam k ρ hk hρ M hM n 0 Δ δ ⟨le_rfl, zero_le_one⟩ ⟨hΔ0.le, hΔ1.le⟩ (by positivity) hsep
  -- TV ≤ 1/2
  have hsymm : tvDist n 0 Δ = tvDist n Δ 0 := by
    unfold tvDist; congr 1; exact Finset.sum_congr rfl (fun b _ => abs_sub_comm _ _)
  have hPD := pinskerDisp n Δ 0 ⟨hΔ0, hΔ1⟩ ⟨le_rfl, zero_le_one⟩
  have hchi := binKL_le_chi2 0 Δ le_rfl zero_le_one hΔ0 hΔ1
  have hTV2 : tvDist n 0 Δ ^ 2 ≤ 1 / 6 := by
    rw [hsymm]
    unfold BanditAlgorithm.bernoulliRelativeEntropy at hPD
    have h1 : (0 - Δ) ^ 2 / (Δ * (1 - Δ)) = Δ / (1 - Δ) := by
      have : (1 - Δ) ≠ 0 := by linarith
      field_simp; ring
    rw [h1] at hchi
    have h2 : Δ / (1 - Δ) ≤ 1 / (3 * n) := by
      rw [div_le_div_iff₀ (by linarith) (by positivity)]
      have := (le_div_iff₀ (by positivity : (0:ℝ) < 4 * n)).mp hΔn
      nlinarith
    calc tvDist n Δ 0 ^ 2 ≤ n / 2 * (0 * Real.log (0 / Δ) + (1 - 0) * Real.log ((1 - 0) / (1 - Δ))) := hPD
      _ ≤ n / 2 * (1 / (3 * n)) := by gcongr; exact hchi.trans h2
      _ = 1 / 6 := by field_simp; ring
  have hTV0 : 0 ≤ tvDist n 0 Δ := by
    unfold tvDist; exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun b _ => abs_nonneg _))
  have hTV : tvDist n 0 Δ ≤ 1 / 2 := by nlinarith
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hLC
  have h12 : (1 : ℝ) / 2 ≤ 1 - tvDist n 0 Δ := by linarith
  have := mul_le_mul_of_nonneg_left h12 (by positivity : 0 ≤ δ / 2)
  calc M * (1 / 8 * β ^ (1 / k) * UniformDRO.Concentration.ck k ρ * Δ ^ (1 / UniformDRO.Concentration.kstar k))
      = δ / 2 * (1 / 2) := by rw [hδ, hS, ha]; ring
    _ ≤ _ := this

open UniformDRO.LowerBound in
theorem solution (k ρ M : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (hM : 0 < M) (n : ℕ) (hn : 0 < n) :
    ENNReal.ofReal (M * max
        (1 / (8 * UniformDRO.Concentration.kstar k * pk k ρ) *
          min (min (Real.sqrt (pk k ρ * (1 - pk k ρ) / (16 * n))) ((1 - pk k ρ) / 2)) (pk k ρ))
        (1 / 8 * βk k ρ ^ (1 / k) * UniformDRO.Concentration.ck k ρ *
          (min (min (1 / (4 * (n : ℝ))) (pk k ρ))
            (1 - (1 - βk k ρ) ^ (1 - UniformDRO.Concentration.kstar k) * pk k ρ)) ^ (1 / UniformDRO.Concentration.kstar k))) ≤
      minimaxRisk k ρ M n := by
  rw [mul_max_of_nonneg _ _ hM.le, ENNReal.ofReal_max]
  exact max_le (theorem3_branch1 k ρ M hk hρ hM n hn) (theorem3_branch2 k ρ M hk hρ hM n hn)
