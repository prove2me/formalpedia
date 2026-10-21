-- Prove2me | solution 1 for SmoothedSimplex.Shadow.measure_P
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:49:21.928158+00:00
-- url     : https://prove2.me/submissions/99b09c8b-2046-49e3-92c1-3ebd78ae92af

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_gaussian
import Definitions.Def_SmoothedSimplex_Shadow_setP

set_option autoImplicit false
open MeasureTheory ProbabilityTheory SmoothedSimplex.Shadow
open scoped RealInnerProductSpace

theorem gint {d : ℕ} {b : ℝ} (hb : 0 < b) :
    ∫ v : EuclideanSpace ℝ (Fin d), Real.exp (-b * ‖v‖ ^ 2) = (Real.pi / b) ^ ((d : ℝ) / 2) := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb, finrank_euclideanSpace_fin]

theorem gint_integrable {d : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : EuclideanSpace ℝ (Fin d) => Real.exp (-b * ‖v‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [gint hb]
  positivity

/-- constant: C * (π/b)^(d/2) with b = 1/(2σ²) - t -/
theorem const_eq {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (κ : ℝ) (hκ : 0 < κ) :
    (1 / (Real.sqrt (2 * Real.pi) * σ)) ^ d * (Real.pi / (1 / (2 * σ ^ 2 * κ))) ^ ((d : ℝ) / 2)
      = κ ^ ((d : ℝ) / 2) := by
  have hs : 0 < Real.sqrt (2 * Real.pi) * σ := by positivity
  have hs2 : (Real.sqrt (2 * Real.pi) * σ) ^ 2 = 2 * Real.pi * σ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have h1 : Real.pi / (1 / (2 * σ ^ 2 * κ)) = κ * (Real.sqrt (2 * Real.pi) * σ) ^ 2 := by
    rw [hs2]; field_simp
  rw [h1, Real.mul_rpow hκ.le (by positivity)]
  have h2 : ((Real.sqrt (2 * Real.pi) * σ) ^ 2) ^ ((d : ℝ) / 2) = (Real.sqrt (2 * Real.pi) * σ) ^ d := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    norm_num
    rw [← Real.rpow_natCast]
    congr 1
    ring
  rw [h2, one_div, inv_pow]
  have : (Real.sqrt (2 * Real.pi) * σ) ^ d ≠ 0 := by positivity
  field_simp

theorem mgf_lintegral {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (κ : ℝ) (hκ : 0 < κ) :
    ∫⁻ x : EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal (Real.exp ((1 / (2 * σ ^ 2)) * (1 - 1 / κ) * ‖x‖ ^ 2) *
        gaussianPdf (0 : EuclideanSpace ℝ (Fin d)) σ x) = ENNReal.ofReal (κ ^ ((d : ℝ) / 2)) := by
  have hb : 0 < 1 / (2 * σ ^ 2 * κ) := by positivity
  have hf : ∀ x : EuclideanSpace ℝ (Fin d), Real.exp ((1 / (2 * σ ^ 2)) * (1 - 1 / κ) * ‖x‖ ^ 2) *
        gaussianPdf (0 : EuclideanSpace ℝ (Fin d)) σ x
      = (1 / (Real.sqrt (2 * Real.pi) * σ)) ^ d * Real.exp (-(1 / (2 * σ ^ 2 * κ)) * ‖x‖ ^ 2) := by
    intro x
    unfold gaussianPdf
    rw [sub_zero]
    have : Real.exp ((1 / (2 * σ ^ 2)) * (1 - 1 / κ) * ‖x‖ ^ 2) *
        Real.exp (-(‖x‖ ^ 2) / (2 * σ ^ 2)) = Real.exp (-(1 / (2 * σ ^ 2 * κ)) * ‖x‖ ^ 2) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    rw [mul_left_comm, this]
  simp_rw [hf]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_const_mul, gint hb, const_eq hσ κ hκ]
  · exact (gint_integrable hb).const_mul _
  · exact Filter.Eventually.of_forall fun x => by positivity

theorem gauss_tail {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (r : ℝ) (hr : 0 ≤ r) (κ : ℝ) (hκ : 1 ≤ κ) :
    gaussian (0 : EuclideanSpace ℝ (Fin d)) σ {x | r ≤ ‖x‖} ≤
      ENNReal.ofReal (Real.exp (-((1 / (2 * σ ^ 2)) * (1 - 1 / κ) * r ^ 2)) * κ ^ ((d : ℝ) / 2)) := by
  have hκ0 : 0 < κ := by linarith
  set t : ℝ := (1 / (2 * σ ^ 2)) * (1 - 1 / κ) with ht
  have ht0 : 0 ≤ t := by
    have : 1 / κ ≤ 1 := by rw [div_le_one hκ0]; exact hκ
    have : 0 ≤ 1 - 1 / κ := by linarith
    positivity
  have hS : MeasurableSet {x : EuclideanSpace ℝ (Fin d) | r ≤ ‖x‖} :=
    measurableSet_le measurable_const measurable_norm
  unfold gaussian
  rw [withDensity_apply _ hS]
  calc ∫⁻ x in {x : EuclideanSpace ℝ (Fin d) | r ≤ ‖x‖},
        ENNReal.ofReal (gaussianPdf (0 : EuclideanSpace ℝ (Fin d)) σ x)
      ≤ ∫⁻ x in {x : EuclideanSpace ℝ (Fin d) | r ≤ ‖x‖},
        ENNReal.ofReal (Real.exp (-(t * r ^ 2))) *
          ENNReal.ofReal (Real.exp (t * ‖x‖ ^ 2) * gaussianPdf (0 : EuclideanSpace ℝ (Fin d)) σ x) := by
        apply setLIntegral_mono' hS
        intro x hx
        have hx' : r ≤ ‖x‖ := hx
        have hpdf : 0 ≤ gaussianPdf (0 : EuclideanSpace ℝ (Fin d)) σ x := by
          unfold gaussianPdf; positivity
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have h1 : 1 ≤ Real.exp (-(t * r ^ 2)) * Real.exp (t * ‖x‖ ^ 2) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp
          have : r ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ hr hx' 2
          nlinarith
        rw [← mul_assoc]
        exact le_mul_of_one_le_left hpdf h1
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (-(t * r ^ 2))) *
          ENNReal.ofReal (Real.exp (t * ‖x‖ ^ 2) * gaussianPdf (0 : EuclideanSpace ℝ (Fin d)) σ x) :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (Real.exp (-(t * r ^ 2))) *
          ∫⁻ x, ENNReal.ofReal (Real.exp (t * ‖x‖ ^ 2) * gaussianPdf (0 : EuclideanSpace ℝ (Fin d)) σ x) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Real.exp (-(t * r ^ 2)) * κ ^ ((d : ℝ) / 2)) := by
        rw [mgf_lintegral hσ κ hκ0, ← ENNReal.ofReal_mul (by positivity)]

theorem gauss_total {d : ℕ} {σ : ℝ} (hσ : 0 < σ) :
    gaussian (0 : EuclideanSpace ℝ (Fin d)) σ Set.univ = 1 := by
  unfold gaussian
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have := mgf_lintegral (d := d) hσ 1 one_pos
  simp only [div_one, sub_self, mul_zero, zero_mul, Real.exp_zero, one_mul, Real.one_rpow] at this
  simpa using this

theorem log6 : (10 : ℝ) * Real.log 6 ≤ 17 * Real.log 3 := by
  have h1 : (10 : ℝ) * Real.log 6 = Real.log (6 ^ 10) := by rw [Real.log_pow]; norm_num
  have h2 : (17 : ℝ) * Real.log 3 = Real.log (3 ^ 17) := by rw [Real.log_pow]; norm_num
  rw [h1, h2]
  exact Real.log_le_log (by norm_num) (by norm_num)

theorem tail_real {d n : ℕ} {σ : ℝ} (hσ : 0 < σ) (hn : 3 ≤ n) :
    Real.exp (-((1 / (2 * σ ^ 2)) * (1 - 1 / (6 : ℝ)) *
        (3 * Real.sqrt ((d : ℝ) * Real.log n) * σ) ^ 2)) * (6 : ℝ) ^ ((d : ℝ) / 2)
      ≤ (n : ℝ) ^ (-(29 / 10 : ℝ) * d) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hlog3 : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have h6 : Real.log 6 ≤ (17 / 10) * Real.log n := by linarith [log6]
  have hr : (3 * Real.sqrt ((d : ℝ) * Real.log n) * σ) ^ 2 = 9 * ((d : ℝ) * Real.log n) * σ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
  rw [hr, Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 6), ← Real.exp_add,
    Real.exp_le_exp]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have e1 : (1 / (2 * σ ^ 2)) * (1 - 1 / (6 : ℝ)) * (9 * ((d : ℝ) * Real.log n) * σ ^ 2)
      = (15 / 4) * ((d : ℝ) * Real.log n) := by
    field_simp; ring
  rw [e1]
  nlinarith [mul_le_mul_of_nonneg_left h6 hd]

theorem chi_part1 {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (n : ℕ) (hn : 3 ≤ n) :
    gaussian (0 : EuclideanSpace ℝ (Fin d)) σ
        {x | 3 * Real.sqrt ((d : ℝ) * Real.log n) * σ ≤ ‖x‖}
      ≤ ENNReal.ofReal ((n : ℝ) ^ (-(29 / 10 : ℝ) * d)) := by
  refine (gauss_tail hσ _ (by positivity) 6 (by norm_num)).trans ?_
  exact ENNReal.ofReal_le_ofReal (tail_real hσ hn)

theorem choose_real {d n : ℕ} (hn : d < n) (hd : 3 ≤ d) :
    (n : ℝ) ^ (-(29 / 10 : ℝ) * d + 1) ≤ (15 / 10000 : ℝ) * ((n.choose d : ℕ) : ℝ)⁻¹ := by
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast (by omega : 4 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  have hC : (0 : ℝ) < (n.choose d : ℕ) := by exact_mod_cast Nat.choose_pos hn.le
  rw [← div_eq_mul_inv, le_div_iff₀ hC]
  have hch : ((n.choose d : ℕ) : ℝ) ≤ (n : ℝ) ^ d / (d.factorial : ℝ) := Nat.choose_le_pow_div d n
  have hf : (6 : ℝ) ≤ (d.factorial : ℝ) := by
    have : Nat.factorial 3 ≤ Nat.factorial d := Nat.factorial_le hd
    have h3 : Nat.factorial 3 = 6 := by decide
    rw [h3] at this
    exact_mod_cast this
  have hy : 0 < (n : ℝ) ^ (-(29 / 10 : ℝ) * d + 1) := Real.rpow_pos_of_pos hn0 _
  have hnd : (n : ℝ) ^ (d : ℕ) = (n : ℝ) ^ (d : ℝ) := (Real.rpow_natCast _ _).symm
  have hmul : (n : ℝ) ^ (-(29 / 10 : ℝ) * d + 1) * (n : ℝ) ^ (d : ℝ) = (n : ℝ) ^ (-(19 / 10 : ℝ) * d + 1) := by
    rw [← Real.rpow_add hn0]; congr 1; ring
  have hexp : (n : ℝ) ^ (-(19 / 10 : ℝ) * d + 1) ≤ (n : ℝ) ^ (-4 : ℤ) := by
    rw [← Real.rpow_intCast]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    push_cast; nlinarith
  have hn4' : (n : ℝ) ^ (-4 : ℤ) ≤ 1 / 256 := by
    rw [zpow_neg, zpow_ofNat]
    rw [one_div]
    apply inv_anti₀ (by norm_num)
    calc (256 : ℝ) = 4 ^ 4 := by norm_num
      _ ≤ (n : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hn4 4
  calc (n : ℝ) ^ (-(29 / 10 : ℝ) * d + 1) * ((n.choose d : ℕ) : ℝ)
      ≤ (n : ℝ) ^ (-(29 / 10 : ℝ) * d + 1) * ((n : ℝ) ^ d / (d.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left hch hy.le
    _ = ((n : ℝ) ^ (-(29 / 10 : ℝ) * d + 1) * (n : ℝ) ^ (d : ℝ)) / (d.factorial : ℝ) := by
        rw [hnd]; ring
    _ ≤ (1 / 256) / 6 := by
        rw [hmul]
        apply div_le_div₀ (by norm_num) (hexp.trans hn4') (by norm_num) hf
    _ ≤ 15 / 10000 := by norm_num

theorem chi_part2 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {σ : ℝ} (hσ : 0 < σ)
    (n : ℕ) (hn : d < n) (hd : 3 ≤ d)
    (P : Measure Ω) (x : Fin n → Ω → EuclideanSpace ℝ (Fin d))
    (hx : ∀ i, AEMeasurable (x i) P) (hmap : ∀ i, P.map (x i) = gaussian 0 σ) :
    P {ω | ∃ i, 3 * Real.sqrt ((d : ℝ) * Real.log n) * σ ≤ ‖x i ω‖}
      ≤ ENNReal.ofReal ((n : ℝ) ^ (-(29 / 10 : ℝ) * d + 1)) := by
  have hn3 : 3 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hS : MeasurableSet {y : EuclideanSpace ℝ (Fin d) |
      3 * Real.sqrt ((d : ℝ) * Real.log n) * σ ≤ ‖y‖} :=
    measurableSet_le measurable_const measurable_norm
  have hset : {ω | ∃ i, 3 * Real.sqrt ((d : ℝ) * Real.log n) * σ ≤ ‖x i ω‖} =
      ⋃ i, (x i) ⁻¹' {y : EuclideanSpace ℝ (Fin d) |
        3 * Real.sqrt ((d : ℝ) * Real.log n) * σ ≤ ‖y‖} := by
    ext ω; simp
  rw [hset]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  have hi : ∀ i : Fin n, P ((x i) ⁻¹' {y : EuclideanSpace ℝ (Fin d) |
        3 * Real.sqrt ((d : ℝ) * Real.log n) * σ ≤ ‖y‖}) ≤
      ENNReal.ofReal ((n : ℝ) ^ (-(29 / 10 : ℝ) * d)) := by
    intro i
    rw [← Measure.map_apply_of_aemeasurable (hx i) hS, hmap i]
    exact chi_part1 hσ n hn3
  calc ∑ i : Fin n, P ((x i) ⁻¹' {y : EuclideanSpace ℝ (Fin d) |
        3 * Real.sqrt ((d : ℝ) * Real.log n) * σ ≤ ‖y‖})
      ≤ ∑ _i : Fin n, ENNReal.ofReal ((n : ℝ) ^ (-(29 / 10 : ℝ) * d)) := Finset.sum_le_sum fun i _ => hi i
    _ = ENNReal.ofReal ((n : ℝ) ^ (-(29 / 10 : ℝ) * d + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.rpow_add_one hn0.ne', ENNReal.ofReal_mul (by positivity)]
        simp [ENNReal.ofReal_natCast, mul_comm]


theorem gauss_shift {d : ℕ} (σ : ℝ) (c : EuclideanSpace ℝ (Fin d)) (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS : MeasurableSet S) :
    gaussian c σ ((fun x => x - c) ⁻¹' S) = gaussian 0 σ S := by
  unfold gaussian
  have hmeas : Measurable fun y : EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (gaussianPdf (0 : EuclideanSpace ℝ (Fin d)) σ y) := by
    unfold gaussianPdf
    fun_prop
  rw [withDensity_apply _ (hS.preimage (measurable_sub_const c)), withDensity_apply _ hS]
  have := (measurePreserving_sub_right (volume : Measure (EuclideanSpace ℝ (Fin d))) c).setLIntegral_comp_preimage
    hS hmeas
  rw [← this]
  congr 1
  ext x
  simp [gaussianPdf]

theorem gauss_prob {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (c : EuclideanSpace ℝ (Fin d)) :
    IsProbabilityMeasure (gaussian c σ) := by
  constructor
  have := gauss_shift σ c Set.univ MeasurableSet.univ
  simpa [gauss_total hσ] using this

theorem solution {d n : ℕ} (hd : 3 ≤ d) (hn : d < n) (σ : ℝ) (hσ : 0 < σ)
    (hσ' : σ ≤ 1 / (3 * Real.sqrt ((d : ℝ) * Real.log n)))
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (habar : ∀ i, ‖abar i‖ ≤ 1) :
    ENNReal.ofReal (1 - (n : ℝ) ^ (-(29 / 10 : ℝ) * d + 1)) ≤
      Measure.pi (fun i => gaussian (abar i) σ) setP := by
  have hn3 : 3 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  haveI : ∀ i, IsProbabilityMeasure (gaussian (abar i) σ) := fun i => gauss_prob hσ (abar i)
  set μ : Measure (Fin n → EuclideanSpace ℝ (Fin d)) := Measure.pi (fun i => gaussian (abar i) σ) with hμ
  have hPm : MeasurableSet (setP : Set (Fin n → EuclideanSpace ℝ (Fin d))) := by
    have : (setP : Set (Fin n → EuclideanSpace ℝ (Fin d))) = ⋂ i, {a | ‖a i‖ ≤ 2} := by
      ext a; simp [setP]
    rw [this]
    exact MeasurableSet.iInter fun i =>
      measurableSet_le ((measurable_pi_apply i).norm) measurable_const
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hsq : 0 < Real.sqrt ((d : ℝ) * Real.log n) := by
    apply Real.sqrt_pos.2
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  have hr : 3 * Real.sqrt ((d : ℝ) * Real.log n) * σ ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hσ'
    linarith
  have hr0 : 0 ≤ 3 * Real.sqrt ((d : ℝ) * Real.log n) * σ := by positivity
  -- complement bound
  have hcompl : μ setPᶜ ≤ ENNReal.ofReal ((n : ℝ) ^ (-(29 / 10 : ℝ) * d + 1)) := by
    have hsub : (setP : Set (Fin n → EuclideanSpace ℝ (Fin d)))ᶜ ⊆
        ⋃ i, (fun a : Fin n → EuclideanSpace ℝ (Fin d) => a i) ⁻¹' {x | 2 < ‖x‖} := by
      intro a ha
      simp only [setP, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le] at ha
      obtain ⟨i, hi⟩ := ha
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans ?_)
    have hi : ∀ i : Fin n, μ ((fun a : Fin n → EuclideanSpace ℝ (Fin d) => a i) ⁻¹' {x | 2 < ‖x‖}) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-(29 / 10 : ℝ) * d)) := by
      intro i
      have hA : MeasurableSet {x : EuclideanSpace ℝ (Fin d) | 2 < ‖x‖} :=
        measurableSet_lt measurable_const measurable_norm
      rw [← Measure.map_apply (measurable_pi_apply i) hA, hμ,
        (measurePreserving_eval (fun i => gaussian (abar i) σ) i).map_eq]
      have hS : MeasurableSet {y : EuclideanSpace ℝ (Fin d) |
          3 * Real.sqrt ((d : ℝ) * Real.log n) * σ ≤ ‖y‖} :=
        measurableSet_le measurable_const measurable_norm
      calc gaussian (abar i) σ {x | 2 < ‖x‖}
          ≤ gaussian (abar i) σ ((fun x => x - abar i) ⁻¹' {y : EuclideanSpace ℝ (Fin d) |
              3 * Real.sqrt ((d : ℝ) * Real.log n) * σ ≤ ‖y‖}) := by
            apply measure_mono
            intro x hx
            simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx ⊢
            have := norm_sub_norm_le x (abar i)
            have h1 := habar i
            have := norm_le_insert' x (abar i)
            have h3 : ‖x‖ - ‖abar i‖ ≤ ‖x - abar i‖ := norm_sub_norm_le x (abar i)
            linarith
        _ = gaussian 0 σ {y | 3 * Real.sqrt ((d : ℝ) * Real.log n) * σ ≤ ‖y‖} :=
            gauss_shift σ (abar i) _ hS
        _ ≤ _ := chi_part1 hσ n hn3
    calc ∑ i : Fin n, μ ((fun a : Fin n → EuclideanSpace ℝ (Fin d) => a i) ⁻¹' {x | 2 < ‖x‖})
        ≤ ∑ _i : Fin n, ENNReal.ofReal ((n : ℝ) ^ (-(29 / 10 : ℝ) * d)) :=
          Finset.sum_le_sum fun i _ => hi i
      _ = ENNReal.ofReal ((n : ℝ) ^ (-(29 / 10 : ℝ) * d + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.rpow_add_one hn0.ne', ENNReal.ofReal_mul (by positivity)]
          simp [ENNReal.ofReal_natCast, mul_comm]
  have hy : 0 ≤ (n : ℝ) ^ (-(29 / 10 : ℝ) * d + 1) := by positivity
  rw [ENNReal.ofReal_sub _ hy, ENNReal.ofReal_one]
  calc 1 - ENNReal.ofReal ((n : ℝ) ^ (-(29 / 10 : ℝ) * d + 1)) ≤ 1 - μ setPᶜ :=
        tsub_le_tsub_left hcompl 1
    _ = μ setP := by
        have := prob_compl_eq_one_sub (μ := μ) hPm.compl
        rw [compl_compl] at this
        exact this.symm
