-- Prove2me | solution 1 for StabGen.Entropy.entropy_regularization_uniform_stability
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T19:10:11.723678+00:00
-- url     : https://prove2.me/submissions/d6dff2c9-e058-48a9-a71d-6f3e0c8c9ca0

import Mathlib
import Definitions.Def_StabGen_Entropy_Model

set_option autoImplicit false

section StabGenEntropyAux

open MeasureTheory InformationTheory StabGen.Entropy

lemma sgE_aux_log (u s : ℝ) (hu : 0 ≤ u) (hs : 0 < s) :
    u * Real.log s - u * Real.log u ≤ 2 * Real.sqrt u * Real.sqrt s - 2 * u := by
  rcases hu.eq_or_lt with rfl | hu
  · simp
  have ha : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hb : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have h1 := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne', Real.log_sqrt hs.le, Real.log_sqrt hu.le] at h1
  have h2 : Real.sqrt u * (Real.sqrt s / Real.sqrt u - 1) = Real.sqrt s - Real.sqrt u := by
    rw [mul_sub, mul_div_cancel₀ _ ha.ne', mul_one]
  have h3 : u * (Real.log s / 2 - Real.log u / 2) ≤ u * (Real.sqrt s / Real.sqrt u - 1) :=
    mul_le_mul_of_nonneg_left h1 hu.le
  have h4 : u * (Real.sqrt s / Real.sqrt u - 1) = Real.sqrt u * (Real.sqrt s - Real.sqrt u) := by
    rw [← h2, ← mul_assoc, Real.mul_self_sqrt hu.le]
  nlinarith [h3, h4, Real.mul_self_sqrt hu.le]

lemma sgE_js_gap (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    2 * klFun ((u + v) / 2) + (Real.sqrt u - Real.sqrt v) ^ 2 / 2 ≤ klFun u + klFun v := by
  rcases (add_nonneg hu hv).eq_or_lt with h | h
  · have hu0 : u = 0 := by linarith
    have hv0 : v = 0 := by linarith
    subst hu0; subst hv0; simp [klFun_zero]; norm_num
  have hs : 0 < (u + v) / 2 := by linarith
  have h1 := sgE_aux_log u _ hu hs
  have h2 := sgE_aux_log v _ hv hs
  simp only [klFun_apply]
  have hss : Real.sqrt ((u + v) / 2) * Real.sqrt ((u + v) / 2) = (u + v) / 2 :=
    Real.mul_self_sqrt hs.le
  have hpp := Real.mul_self_sqrt hu
  have hqq := Real.mul_self_sqrt hv
  have hp := Real.sqrt_nonneg u
  have hq := Real.sqrt_nonneg v
  have hw := Real.sqrt_nonneg ((u + v) / 2)
  nlinarith [sq_nonneg (2 * Real.sqrt ((u + v) / 2) - (Real.sqrt u + Real.sqrt v))]

lemma sgE_js_gap_w (c a b : ℝ) (hc : 0 < c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * (c * klFun ((a + b) / 2 / c)) + (Real.sqrt a - Real.sqrt b) ^ 2 / 2 ≤
      c * klFun (a / c) + c * klFun (b / c) := by
  have h := sgE_js_gap (a / c) (b / c) (div_nonneg ha hc.le) (div_nonneg hb hc.le)
  have e1 : (a / c + b / c) / 2 = (a + b) / 2 / c := by ring
  rw [e1] at h
  have e2 : c * (Real.sqrt (a / c) - Real.sqrt (b / c)) ^ 2 = (Real.sqrt a - Real.sqrt b) ^ 2 := by
    rw [Real.sqrt_div' a hc.le, Real.sqrt_div' b hc.le, ← sub_div, div_pow, Real.sq_sqrt hc.le]
    have hc' := hc.ne'
    field_simp
  have h' := mul_le_mul_of_nonneg_left h hc.le
  nlinarith [h', e2]

lemma sgE_amgm_pt (r M a b t : ℝ) (hr0 : 0 ≤ r) (hrM : r ≤ M) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht : 0 < t) :
    r * a - r * b ≤ t * (M ^ 2 / 4) * (a + b) +
      ((Real.sqrt a - Real.sqrt b) ^ 2 / (2 * t) + M / 2 * (a - b)) := by
  set p := Real.sqrt a with hp_def
  set q := Real.sqrt b with hq_def
  have hpa : p ^ 2 = a := Real.sq_sqrt ha
  have hqb : q ^ 2 = b := Real.sq_sqrt hb
  set h := r - M / 2 with hh_def
  have hh : h ^ 2 ≤ M ^ 2 / 4 := by nlinarith
  have e1 : h ^ 2 * (p + q) ^ 2 ≤ (M ^ 2 / 4) * (2 * (p ^ 2 + q ^ 2)) :=
    mul_le_mul hh (by nlinarith [sq_nonneg (p - q)]) (sq_nonneg _) (by positivity)
  have e2 := mul_le_mul_of_nonneg_left e1 (sq_nonneg t)
  have key : 2 * t * (h * (p ^ 2 - q ^ 2)) ≤
      t ^ 2 * ((M ^ 2 / 4) * (2 * (p ^ 2 + q ^ 2))) + (p - q) ^ 2 := by
    nlinarith [sq_nonneg (t * h * (p + q) - (p - q))]
  have : r * a - r * b - M / 2 * (a - b) - t * (M ^ 2 / 4) * (a + b) ≤ (p - q) ^ 2 / (2 * t) := by
    rw [le_div_iff₀ (by positivity)]
    rw [← hpa, ← hqb]
    have : r = h + M / 2 := by rw [hh_def]; ring
    rw [this]
    nlinarith [key]
  linarith

lemma sgE_ae_zero_of_ac {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) (g f0 : Θ → ℝ)
    (hg : Measurable g) (hf0 : Measurable f0) (hf0n : ∀ θ, 0 ≤ f0 θ) (hgn : ∀ θ, 0 ≤ g θ)
    (hac : ν.withDensity (fun θ => ENNReal.ofReal (g θ)) ≪
      ν.withDensity (fun θ => ENNReal.ofReal (f0 θ))) :
    ∀ᵐ θ ∂ν, f0 θ = 0 → g θ = 0 := by
  have h1 : ∀ᵐ θ ∂ν.withDensity (fun θ => ENNReal.ofReal (f0 θ)), 0 < f0 θ := by
    rw [ae_withDensity_iff hf0.ennreal_ofReal]
    refine ae_of_all _ (fun θ hθ => ?_)
    rcases (hf0n θ).eq_or_lt with h | h
    · exfalso; apply hθ; rw [← h]; simp
    · exact h
  have h2 : ∀ᵐ θ ∂ν.withDensity (fun θ => ENNReal.ofReal (g θ)), 0 < f0 θ := hac.ae_le h1
  rw [ae_withDensity_iff hg.ennreal_ofReal] at h2
  filter_upwards [h2] with θ hθ h0
  by_contra hne
  have hpos : 0 < g θ := lt_of_le_of_ne (hgn θ) (Ne.symm hne)
  have := hθ (ENNReal.ofReal_pos.2 hpos).ne'
  linarith

lemma sgE_kl_repr {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) (g f0 : Θ → ℝ)
    (hg : Measurable g) (hf0 : Measurable f0) (hf0n : ∀ θ, 0 ≤ f0 θ) (hgn : ∀ θ, 0 ≤ g θ)
    (hgi : Integrable g ν) (hf0i : Integrable f0 ν)
    (hz : ∀ᵐ θ ∂ν, f0 θ = 0 → g θ = 0) :
    relEntropy ν g f0 = ∫⁻ θ, ENNReal.ofReal (f0 θ * klFun (g θ / f0 θ)) ∂ν := by
  set π := ν.withDensity (fun θ => ENNReal.ofReal (f0 θ)) with hπ
  set μ := ν.withDensity (fun θ => ENNReal.ofReal (g θ)) with hμ
  have : IsFiniteMeasure π := isFiniteMeasure_withDensity_ofReal hf0i.2
  have : IsFiniteMeasure μ := isFiniteMeasure_withDensity_ofReal hgi.2
  have hφm : Measurable (fun θ => ENNReal.ofReal (g θ / f0 θ)) := (hg.div hf0).ennreal_ofReal
  have heq : μ = π.withDensity (fun θ => ENNReal.ofReal (g θ / f0 θ)) := by
    rw [hπ, hμ, ← withDensity_mul ν hf0.ennreal_ofReal hφm]
    apply withDensity_congr_ae
    filter_upwards [hz] with θ hθ
    simp only [Pi.mul_apply]
    rcases (hf0n θ).eq_or_lt with h | h
    · rw [hθ h.symm, ← h]; simp
    · rw [← ENNReal.ofReal_mul (hf0n θ), mul_div_cancel₀ _ h.ne']
  have hac : μ ≪ π := heq ▸ withDensity_absolutelyContinuous _ _
  show klDiv μ π = _
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  have hrn : μ.rnDeriv π =ᵐ[π] fun θ => ENNReal.ofReal (g θ / f0 θ) := by
    rw [heq]; exact Measure.rnDeriv_withDensity π hφm
  have hkm : Measurable (fun θ => ENNReal.ofReal (klFun (g θ / f0 θ))) :=
    (measurable_klFun.comp (hg.div hf0)).ennreal_ofReal
  calc ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv π x).toReal) ∂π
      = ∫⁻ x, ENNReal.ofReal (klFun (g x / f0 x)) ∂π := by
        apply lintegral_congr_ae
        filter_upwards [hrn] with x hx
        rw [hx, ENNReal.toReal_ofReal (div_nonneg (hgn x) (hf0n x))]
    _ = ∫⁻ θ, ENNReal.ofReal (f0 θ * klFun (g θ / f0 θ)) ∂ν := by
        rw [hπ, lintegral_withDensity_eq_lintegral_mul ν hf0.ennreal_ofReal hkm]
        apply lintegral_congr
        intro θ
        simp only [Pi.mul_apply]
        rw [ENNReal.ofReal_mul (hf0n θ)]

lemma sgE_toReal_ineq (a b c d : ENNReal) (hc : c ≠ ⊤) (hd : d ≠ ⊤) (h : 2 * a + b ≤ c + d) :
    a ≠ ⊤ ∧ 2 * a.toReal + b.toReal ≤ c.toReal + d.toReal := by
  have hcd : c + d ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hc, hd⟩
  have h1 : 2 * a + b ≠ ⊤ := ne_top_of_le_ne_top hcd h
  obtain ⟨h2, hb⟩ := ENNReal.add_ne_top.1 h1
  refine ⟨fun ha => by rw [ha] at h2; simp at h2, ?_⟩
  have := ENNReal.toReal_mono hcd h
  rwa [ENNReal.toReal_add h2 hb, ENNReal.toReal_add hc hd, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat] at this

lemma sgE_risk_toReal (x y lam : ℝ) (a b : ENNReal)
    (h : ENNReal.ofReal x + ENNReal.ofReal lam * a ≤ ENNReal.ofReal y + ENNReal.ofReal lam * b)
    (hl : 0 < lam) (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x + lam * a.toReal ≤ y + lam * b.toReal := by
  have hR : ENNReal.ofReal y + ENNReal.ofReal lam * b ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb⟩
  have := ENNReal.toReal_mono hR h
  rwa [ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha),
    ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hx, ENNReal.toReal_ofReal hy,
    ENNReal.toReal_ofReal hl.le] at this

lemma sgE_int_rmul {Θ Z : Type*} [MeasurableSpace Θ] (ν : Measure Θ) (r : Θ → Z → ℝ) (M : ℝ)
    (hr_meas : ∀ z, Measurable (fun θ => r θ z)) (hr : ∀ θ z, 0 ≤ r θ z ∧ r θ z ≤ M)
    (g : Θ → ℝ) (hg : IsDensity ν g) (z : Z) : Integrable (fun θ => r θ z * g θ) ν :=
  hg.2.2.1.bdd_mul (hr_meas z).aestronglyMeasurable
    (ae_of_all _ fun θ => by rw [Real.norm_eq_abs, abs_of_nonneg (hr θ z).1]; exact (hr θ z).2)

lemma sgE_int_H {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) (p q : Θ → ℝ)
    (hp : IsDensity ν p) (hq : IsDensity ν q) :
    Integrable (fun θ => (Real.sqrt (p θ) - Real.sqrt (q θ)) ^ 2) ν := by
  refine Integrable.mono' (hp.2.2.1.add hq.2.2.1)
    ((hp.1.sqrt.sub hq.1.sqrt).pow_const 2).aestronglyMeasurable (ae_of_all _ fun θ => ?_)
  have ha := hp.2.1 θ
  have hb := hq.2.1 θ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp only [Pi.add_apply]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
    mul_nonneg (Real.sqrt_nonneg (p θ)) (Real.sqrt_nonneg (q θ))]

lemma sgE_amgm_int {Θ Z : Type*} [MeasurableSpace Θ] (ν : Measure Θ) (r : Θ → Z → ℝ) (M : ℝ)
    (hr_meas : ∀ z, Measurable (fun θ => r θ z)) (hr : ∀ θ z, 0 ≤ r θ z ∧ r θ z ≤ M)
    (p q : Θ → ℝ) (hp : IsDensity ν p) (hq : IsDensity ν q) (z : Z) (t : ℝ) (ht : 0 < t) :
    avgLoss ν r p z - avgLoss ν r q z ≤
      t * M ^ 2 / 2 + (∫ θ, (Real.sqrt (p θ) - Real.sqrt (q θ)) ^ 2 ∂ν) / (2 * t) := by
  have hpi := hp.2.2.1
  have hqi := hq.2.2.1
  have hH := sgE_int_H ν p q hp hq
  have i1 : Integrable (fun θ => t * (M ^ 2 / 4) * (p θ + q θ)) ν := (hpi.add hqi).const_mul _
  have i2 : Integrable (fun θ => (Real.sqrt (p θ) - Real.sqrt (q θ)) ^ 2 / (2 * t)) ν :=
    hH.div_const _
  have i3 : Integrable (fun θ => M / 2 * (p θ - q θ)) ν := (hpi.sub hqi).const_mul _
  have i23 : Integrable (fun θ => (Real.sqrt (p θ) - Real.sqrt (q θ)) ^ 2 / (2 * t) +
      M / 2 * (p θ - q θ)) ν := i2.add i3
  have h1 : ∫ θ, (r θ z * p θ - r θ z * q θ) ∂ν ≤
      ∫ θ, (t * (M ^ 2 / 4) * (p θ + q θ) +
        ((Real.sqrt (p θ) - Real.sqrt (q θ)) ^ 2 / (2 * t) + M / 2 * (p θ - q θ))) ∂ν := by
    apply integral_mono ((sgE_int_rmul ν r M hr_meas hr p hp z).sub (sgE_int_rmul ν r M hr_meas hr q hq z))
    · exact i1.add i23
    · intro θ
      exact sgE_amgm_pt (r θ z) M (p θ) (q θ) t (hr θ z).1 (hr θ z).2 (hp.2.1 θ) (hq.2.1 θ) ht
  rw [integral_sub (sgE_int_rmul ν r M hr_meas hr p hp z) (sgE_int_rmul ν r M hr_meas hr q hq z),
    integral_add i1 i23, integral_add i2 i3, integral_const_mul, integral_div, integral_const_mul,
    integral_add hpi hqi, integral_sub hpi hqi, hp.2.2.2, hq.2.2.2] at h1
  unfold avgLoss
  linarith

end StabGenEntropyAux

open MeasureTheory InformationTheory StabGen.Entropy in
theorem solution {Θ Z : Type*} [MeasurableSpace Θ]
    (ν : Measure Θ) [SigmaFinite ν]
    (r : Θ → Z → ℝ) (M : ℝ)
    (hr_meas : ∀ z, Measurable (fun θ => r θ z))
    (hr : ∀ θ z, 0 ≤ r θ z ∧ r θ z ≤ M)
    (f0 : Θ → ℝ) (hf0 : IsDensity ν f0) (lam : ℝ) (hlam : 0 < lam)
    {m : ℕ} (S : Fin m → Z) (i : Fin m) (f f' : Θ → ℝ)
    (hf : IsDensity ν f)
    (hfmin : ∀ g, IsDensity ν g → entropyRegRisk ν r f0 lam S f ≤ entropyRegRisk ν r f0 lam S g)
    (hf' : IsDensity ν f')
    (hf'min : ∀ g, IsDensity ν g →
      truncEntropyRegRisk ν r f0 lam S i f' ≤ truncEntropyRegRisk ν r f0 lam S i g) :
    ∀ z : Z, |avgLoss ν r f z - avgLoss ν r f' z| ≤ M ^ 2 / (lam * (m : ℝ)) := by
  intro z
  have hm : (0 : ℝ) < m := by exact_mod_cast Fin.pos i
  have hc : 0 < lam * (m : ℝ) := mul_pos hlam hm
  -- the midpoint density
  set g : Θ → ℝ := fun θ => (f θ + f' θ) / 2 with hgdef
  have hg : IsDensity ν g := by
    refine ⟨(hf.1.add hf'.1).div_const 2, fun θ => div_nonneg (add_nonneg (hf.2.1 θ) (hf'.2.1 θ))
      zero_le_two, (hf.2.2.1.add hf'.2.2.1).div_const 2, ?_⟩
    simp only [hgdef]
    rw [integral_div, integral_add hf.2.2.1 hf'.2.2.1, hf.2.2.2, hf'.2.2.2]; norm_num
  have havg : ∀ z', avgLoss ν r g z' = (avgLoss ν r f z' + avgLoss ν r f' z') / 2 := by
    intro z'
    unfold avgLoss
    rw [← integral_add (sgE_int_rmul ν r M hr_meas hr f hf z') (sgE_int_rmul ν r M hr_meas hr f' hf' z'),
      ← integral_div]
    congr 1; funext θ; simp only [hgdef]; ring
  have havg_nn : ∀ p, IsDensity ν p → ∀ z', 0 ≤ avgLoss ν r p z' := fun p hp z' =>
    integral_nonneg fun θ => mul_nonneg (hr θ z').1 (hp.2.1 θ)
  -- finiteness of the relative entropies
  have : IsFiniteMeasure (ν.withDensity (fun θ => ENNReal.ofReal (f0 θ))) :=
    isFiniteMeasure_withDensity_ofReal hf0.2.2.1.2
  have hK0 : relEntropy ν f0 f0 = 0 := klDiv_self _
  have hl0 : ENNReal.ofReal lam ≠ 0 := (ENNReal.ofReal_pos.2 hlam).ne'
  have hKf : relEntropy ν f f0 ≠ ⊤ := by
    intro h
    have := hfmin f0 hf0
    unfold entropyRegRisk at this
    rw [h, hK0, ENNReal.mul_top hl0, add_top, mul_zero, add_zero, top_le_iff] at this
    exact ENNReal.ofReal_ne_top this
  have hKf' : relEntropy ν f' f0 ≠ ⊤ := by
    intro h
    have := hf'min f0 hf0
    unfold truncEntropyRegRisk at this
    rw [h, hK0, ENNReal.mul_top hl0, add_top, mul_zero, add_zero, top_le_iff] at this
    exact ENNReal.ofReal_ne_top this
  have hacf := hKf
  unfold relEntropy at hacf
  have hacf' := hKf'
  unfold relEntropy at hacf'
  have hzf := sgE_ae_zero_of_ac ν f f0 hf.1 hf0.1 hf0.2.1 hf.2.1 (klDiv_ne_top_iff.1 hacf).1
  have hzf' := sgE_ae_zero_of_ac ν f' f0 hf'.1 hf0.1 hf0.2.1 hf'.2.1 (klDiv_ne_top_iff.1 hacf').1
  have hzg : ∀ᵐ θ ∂ν, f0 θ = 0 → g θ = 0 := by
    filter_upwards [hzf, hzf'] with θ h1 h2 h0
    simp only [hgdef, h1 h0, h2 h0]; norm_num
  have rf := sgE_kl_repr ν f f0 hf.1 hf0.1 hf0.2.1 hf.2.1 hf.2.2.1 hf0.2.2.1 hzf
  have rf' := sgE_kl_repr ν f' f0 hf'.1 hf0.1 hf0.2.1 hf'.2.1 hf'.2.2.1 hf0.2.2.1 hzf'
  have rg := sgE_kl_repr ν g f0 hg.1 hf0.1 hf0.2.1 hg.2.1 hg.2.2.1 hf0.2.2.1 hzg
  -- the pointwise Jensen-Shannon gap
  have hFm : ∀ p : Θ → ℝ, Measurable p →
      Measurable (fun θ => ENNReal.ofReal (f0 θ * klFun (p θ / f0 θ))) := fun p hp =>
    (hf0.1.mul (measurable_klFun.comp (hp.div hf0.1))).ennreal_ofReal
  have hHm : Measurable (fun θ => ENNReal.ofReal ((Real.sqrt (f θ) - Real.sqrt (f' θ)) ^ 2 / 2)) :=
    (((hf.1.sqrt.sub hf'.1.sqrt).pow_const 2).div_const 2).ennreal_ofReal
  have hpt : ∀ᵐ θ ∂ν, 2 * ENNReal.ofReal (f0 θ * klFun (g θ / f0 θ)) +
      ENNReal.ofReal ((Real.sqrt (f θ) - Real.sqrt (f' θ)) ^ 2 / 2) ≤
      ENNReal.ofReal (f0 θ * klFun (f θ / f0 θ)) + ENNReal.ofReal (f0 θ * klFun (f' θ / f0 θ)) := by
    filter_upwards [hzf, hzf'] with θ h1 h2
    have hgθ : g θ = (f θ + f' θ) / 2 := rfl
    rcases (hf0.2.1 θ).eq_or_lt with h | h
    · rw [hgθ, ← h, h1 h.symm, h2 h.symm]; simp
    · have key := sgE_js_gap_w (f0 θ) (f θ) (f' θ) h (hf.2.1 θ) (hf'.2.1 θ)
      have n1 : 0 ≤ f0 θ * klFun (g θ / f0 θ) :=
        mul_nonneg h.le (klFun_nonneg (div_nonneg (hg.2.1 θ) h.le))
      have n2 : 0 ≤ f0 θ * klFun (f θ / f0 θ) :=
        mul_nonneg h.le (klFun_nonneg (div_nonneg (hf.2.1 θ) h.le))
      have n3 : 0 ≤ f0 θ * klFun (f' θ / f0 θ) :=
        mul_nonneg h.le (klFun_nonneg (div_nonneg (hf'.2.1 θ) h.le))
      have n4 : 0 ≤ (Real.sqrt (f θ) - Real.sqrt (f' θ)) ^ 2 / 2 := by positivity
      rw [show (2 : ENNReal) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by positivity) n4, ← ENNReal.ofReal_add n2 n3]
      apply ENNReal.ofReal_le_ofReal
      rw [hgθ]; exact key
  have hint_ineq : 2 * relEntropy ν g f0 +
      ∫⁻ θ, ENNReal.ofReal ((Real.sqrt (f θ) - Real.sqrt (f' θ)) ^ 2 / 2) ∂ν ≤
      relEntropy ν f f0 + relEntropy ν f' f0 := by
    rw [rg, rf, rf']
    calc 2 * ∫⁻ θ, ENNReal.ofReal (f0 θ * klFun (g θ / f0 θ)) ∂ν +
          ∫⁻ θ, ENNReal.ofReal ((Real.sqrt (f θ) - Real.sqrt (f' θ)) ^ 2 / 2) ∂ν
        = ∫⁻ θ, (2 * ENNReal.ofReal (f0 θ * klFun (g θ / f0 θ)) +
            ENNReal.ofReal ((Real.sqrt (f θ) - Real.sqrt (f' θ)) ^ 2 / 2)) ∂ν := by
          rw [lintegral_add_left ((hFm g hg.1).const_mul 2), lintegral_const_mul _ (hFm g hg.1)]
      _ ≤ ∫⁻ θ, (ENNReal.ofReal (f0 θ * klFun (f θ / f0 θ)) +
            ENNReal.ofReal (f0 θ * klFun (f' θ / f0 θ))) ∂ν := lintegral_mono_ae hpt
      _ = _ := by rw [lintegral_add_left (hFm f hf.1)]
  have hHi := sgE_int_H ν f f' hf hf'
  have ht : 0 < 1 / (lam * (m : ℝ)) := by positivity
  have ai := sgE_amgm_int ν r M hr_meas hr f' f hf' hf (S i) _ ht
  have az1 := sgE_amgm_int ν r M hr_meas hr f f' hf hf' z _ ht
  have az2 := sgE_amgm_int ν r M hr_meas hr f' f hf' hf z _ ht
  have hsym : ∫ θ, (Real.sqrt (f' θ) - Real.sqrt (f θ)) ^ 2 ∂ν =
      ∫ θ, (Real.sqrt (f θ) - Real.sqrt (f' θ)) ^ 2 ∂ν := by
    congr 1; funext θ; ring
  rw [hsym] at ai az2
  have hHlin : ∫⁻ θ, ENNReal.ofReal ((Real.sqrt (f θ) - Real.sqrt (f' θ)) ^ 2 / 2) ∂ν =
      ENNReal.ofReal ((∫ θ, (Real.sqrt (f θ) - Real.sqrt (f' θ)) ^ 2 ∂ν) / 2) := by
    rw [← integral_div, ofReal_integral_eq_lintegral_ofReal (hHi.div_const 2)
      (ae_of_all _ fun θ => by positivity)]
  have hHn_nn : 0 ≤ ∫ θ, (Real.sqrt (f θ) - Real.sqrt (f' θ)) ^ 2 ∂ν :=
    integral_nonneg fun θ => sq_nonneg _
  rw [hHlin] at hint_ineq
  obtain ⟨hKg, hjs⟩ := sgE_toReal_ineq _ _ _ _ hKf hKf' hint_ineq
  rw [ENNReal.toReal_ofReal (div_nonneg hHn_nn zero_le_two)] at hjs
  -- minimality, in real form
  have h1 := hfmin g hg
  unfold entropyRegRisk at h1
  have h2 := hf'min g hg
  unfold truncEntropyRegRisk at h2
  have m1 := sgE_risk_toReal _ _ _ _ _ h1 hlam hKf hKg
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => havg_nn f hf (S j)))
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => havg_nn g hg (S j)))
  have m2 := sgE_risk_toReal _ _ _ _ _ h2 hlam hKf' hKg
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => havg_nn f' hf' (S j)))
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => havg_nn g hg (S j)))
  have hSf : ∑ j, avgLoss ν r f (S j) =
      avgLoss ν r f (S i) + ∑ j ∈ Finset.univ.erase i, avgLoss ν r f (S j) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hSf' : ∑ j, avgLoss ν r f' (S j) =
      avgLoss ν r f' (S i) + ∑ j ∈ Finset.univ.erase i, avgLoss ν r f' (S j) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hSg : ∑ j, avgLoss ν r g (S j) =
      (∑ j, avgLoss ν r f (S j) + ∑ j, avgLoss ν r f' (S j)) / 2 := by
    simp only [havg]; rw [← Finset.sum_div, Finset.sum_add_distrib]
  have hTg : ∑ j ∈ Finset.univ.erase i, avgLoss ν r g (S j) =
      (∑ j ∈ Finset.univ.erase i, avgLoss ν r f (S j) +
        ∑ j ∈ Finset.univ.erase i, avgLoss ν r f' (S j)) / 2 := by
    simp only [havg]; rw [← Finset.sum_div, Finset.sum_add_distrib]
  rw [hSg, hSf, hSf'] at m1
  rw [hTg] at m2
  have e1 : 1 / (lam * (m : ℝ)) * M ^ 2 / 2 = M ^ 2 / (lam * (m : ℝ)) / 2 := by ring
  have e2 : (∫ θ, (Real.sqrt (f θ) - Real.sqrt (f' θ)) ^ 2 ∂ν) / (2 * (1 / (lam * (m : ℝ)))) =
      lam * (m : ℝ) * (∫ θ, (Real.sqrt (f θ) - Real.sqrt (f' θ)) ^ 2 ∂ν) / 2 := by
    field_simp
  rw [e1, e2] at ai az1 az2
  have kk : ∀ a b : ℝ, (m : ℝ) * (1 / (m : ℝ) * a + lam * b) = a + lam * (m : ℝ) * b := by
    intro a b
    rw [mul_add, ← mul_assoc, mul_one_div_cancel hm.ne', one_mul]; ring
  have m1' := mul_le_mul_of_nonneg_left m1 hm.le
  have m2' := mul_le_mul_of_nonneg_left m2 hm.le
  rw [kk, kk] at m1' m2'
  have hjs' := mul_le_mul_of_nonneg_left hjs hc.le
  rw [abs_le]
  constructor <;> linarith [m1', m2', hjs', ai, az1, az2]
