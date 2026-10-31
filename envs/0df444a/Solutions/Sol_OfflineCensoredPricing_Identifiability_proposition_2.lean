-- Prove2me | solution 1 for OfflineCensoredPricing.Identifiability.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T17:27:02.362542+00:00
-- url     : https://prove2.me/submissions/a5c60a78-8f1c-4141-a7d5-666e92db5b0e

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model

open MeasureTheory Set OfflineCensoredPricing.Identifiability

namespace OCPProp2Aux

lemma lam_pos {K : ℕ} (I : Instance K) (hI : I.Standing) : 0 < lam I := by
  obtain ⟨-, -, hplo, -, hblo, hbb, -, hK, -, hpi, hyh, -⟩ := hI
  have i : Fin K := ⟨0, by omega⟩
  have hle : I.yh i + I.b * I.p i ≤ lam I :=
    le_ciSup (Finite.bddAbove_range (fun i => I.yh i + I.b * I.p i)) i
  have hb : 0 < I.b := lt_of_lt_of_le hblo hbb
  have hp : 0 < I.p i := lt_of_lt_of_le hplo (hpi i).1
  have := hyh i
  have := mul_pos hb hp
  linarith

lemma ae_lower {K : ℕ} (I : Instance K) (hI : I.Standing) (μ : Measure ℝ) (hμ : μ ∈ Amb I) :
    ∀ᵐ ξ ∂μ, min (lam I) (I.b * I.phi) ≤ ξ := by
  set m := min (lam I) (I.b * I.phi) with hmdef
  have hnull : ∀ n : ℕ, μ (Iic (m - 1 / ((n : ℝ) + 1))) = 0 := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hx1 : m - 1 / ((n : ℝ) + 1) < lam I := by
      have := min_le_left (lam I) (I.b * I.phi); linarith
    have hx2 : m - 1 / ((n : ℝ) + 1) < I.b * I.phi := by
      have := min_le_right (lam I) (I.b * I.phi); linarith
    rw [hμ.2 _ hx1]
    exact measure_mono_null (Iic_subset_Iio.2 hx2) hI.2.2.2.2.2.2.2.2.2.2.2.1
  have hall : ∀ᵐ ξ ∂μ, ∀ n : ℕ, ξ ∉ Iic (m - 1 / ((n : ℝ) + 1)) :=
    ae_all_iff.2 (fun n => measure_eq_zero_iff_ae_notMem.1 (hnull n))
  filter_upwards [hall] with ξ hξ
  by_contra h
  push_neg at h
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
  exact hξ n (show ξ ≤ m - 1 / ((n : ℝ) + 1) by linarith)

/-- `min (ξ − c) y` is integrable under any probability law with an a.s. lower bound. -/
lemma integrable_min' (μ : Measure ℝ) [IsProbabilityMeasure μ] (m c y : ℝ)
    (hm : ∀ᵐ ξ ∂μ, m ≤ ξ) : Integrable (fun ξ => min (ξ - c) y) μ := by
  refine Integrable.of_bound (by fun_prop) (|y| + |m - c|) ?_
  filter_upwards [hm] with ξ hξ
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have : min (m - c) y ≤ min (ξ - c) y := min_le_min_right _ (by linarith)
    have h1 : -(|y| + |m - c|) ≤ min (m - c) y := by
      rcases min_cases (m - c) y with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
        linarith [neg_abs_le y, neg_abs_le (m - c), abs_nonneg y, abs_nonneg (m - c)]
    linarith
  · linarith [min_le_right (ξ - c) y, le_abs_self y, abs_nonneg (m - c)]

lemma Iio_eq_iUnion (l : ℝ) : Iio l = ⋃ n : ℕ, Iic (l - 1 / ((n : ℝ) + 1)) := by
  ext x
  simp only [mem_Iio, mem_iUnion, mem_Iic]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
    exact ⟨n, by linarith⟩
  · rintro ⟨n, hn⟩
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

lemma mono_Iic (l : ℝ) : Monotone (fun n : ℕ => Iic (l - 1 / ((n : ℝ) + 1))) := by
  intro n n' h
  apply Iic_subset_Iic.2
  have : 1 / ((n' : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1)
  linarith

lemma restrict_eq {K : ℕ} (I : Instance K) (μ : Measure ℝ) (hμ : μ ∈ Amb I) :
    μ.restrict (Iio (lam I)) = I.μξ.restrict (Iio (lam I)) := by
  haveI : IsProbabilityMeasure μ := hμ.1
  refine Measure.ext_of_Iic _ _ (fun a => ?_)
  rw [Measure.restrict_apply measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  rcases lt_or_ge a (lam I) with h | h
  · rw [inter_eq_left.2 (Iic_subset_Iio.2 h)]
    exact hμ.2 a h
  · have hsub : Iio (lam I) ⊆ Iic a := fun x hx => le_of_lt (lt_of_lt_of_le hx h)
    rw [inter_eq_right.2 hsub, Iio_eq_iUnion,
      (mono_Iic _).measure_iUnion, (mono_Iic _).measure_iUnion]
    congr 1
    funext n
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact hμ.2 _ (by linarith)

lemma Iio_eq {K : ℕ} (I : Instance K) (μ : Measure ℝ) (hμ : μ ∈ Amb I) :
    μ (Iio (lam I)) = I.μξ (Iio (lam I)) := by
  have := congrArg (fun ν : Measure ℝ => ν univ) (restrict_eq I μ hμ)
  simpa using this

/-- Splitting an integral at `λ`: the part below `λ` is the same for every law in `𝓕`. -/
lemma split {K : ℕ} (I : Instance K) (μ : Measure ℝ) (hμ : μ ∈ Amb I) (f : ℝ → ℝ)
    (hf : Integrable f μ) :
    ∫ ξ, f ξ ∂μ = ∫ ξ in Iio (lam I), f ξ ∂I.μξ + ∫ ξ in Ici (lam I), f ξ ∂μ := by
  rw [← integral_add_compl measurableSet_Iio hf, compl_Iio, restrict_eq I μ hμ]

lemma real_Ici {K : ℕ} (I : Instance K) (hP : IsProbabilityMeasure I.μξ) (μ : Measure ℝ)
    (hμ : μ ∈ Amb I) : μ.real (Ici (lam I)) = 1 - gam I := by
  haveI : IsProbabilityMeasure μ := hμ.1
  rw [← compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio]
  unfold gam
  rw [measureReal_def, measureReal_def, Iio_eq I μ hμ]

/-- The two-point-type laws `μξ|_{(−∞,λ)} + P[ξ ≥ λ] δ_c`, `c ≥ λ`, lie in the ambiguity set. -/
noncomputable def witness {K : ℕ} (I : Instance K) (c : ℝ) : Measure ℝ :=
  I.μξ.restrict (Iio (lam I)) + I.μξ (Ici (lam I)) • Measure.dirac c

lemma witness_mem {K : ℕ} (I : Instance K) (hP : IsProbabilityMeasure I.μξ) (c : ℝ)
    (hc : lam I ≤ c) : witness I c ∈ Amb I := by
  refine ⟨⟨?_⟩, fun x hx => ?_⟩
  · unfold witness
    rw [Measure.add_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ c), smul_eq_mul, mul_one,
      ← compl_Iio, measure_add_measure_compl measurableSet_Iio, measure_univ]
  · unfold witness
    rw [Measure.add_apply, Measure.restrict_apply measurableSet_Iic,
      inter_eq_left.2 (Iic_subset_Iio.2 hx), Measure.smul_apply,
      Measure.dirac_apply' _ measurableSet_Iic, indicator_of_notMem (show c ∉ Iic x by
        simp only [mem_Iic, not_le]; linarith), smul_eq_mul, mul_zero, add_zero]

lemma integral_witness {K : ℕ} (I : Instance K) (hP : IsProbabilityMeasure I.μξ) (c : ℝ)
    (f : ℝ → ℝ) (hf : Integrable f I.μξ) :
    ∫ ξ, f ξ ∂(witness I c) = ∫ ξ in Iio (lam I), f ξ ∂I.μξ + (1 - gam I) * f c := by
  unfold witness
  have hne : I.μξ (Ici (lam I)) ≠ ⊤ := measure_ne_top _ _
  rw [integral_add_measure hf.restrict
      ((integrable_dirac (by simp)).smul_measure hne),
    integral_smul_measure, integral_dirac, smul_eq_mul]
  congr 2
  rw [← compl_Iio, ← measureReal_def, probReal_compl_eq_one_sub measurableSet_Iio]
  rfl

end OCPProp2Aux

open OCPProp2Aux in
theorem solution {K : ℕ} (I : Instance K) (hI : I.Standing) (q : ℝ)
    (hq : q ∈ Icc I.plo I.phi) :
    IsGreatest ((fun μ => RF I μ q) '' Amb I)
        (if q < pTilde I then RF I I.μξ q else R1 I q) ∧
      IsLeast ((fun μ => RF I μ q) '' Amb I)
        (if q < pTilde I then RF I I.μξ q else R2 I q) ∧
      Rmax I q = (if q < pTilde I then RF I I.μξ q else R1 I q) ∧
      Rmin I q = (if q < pTilde I then RF I I.μξ q else R2 I q) := by
  have hlower := ae_lower I hI
  have hlam := lam_pos I hI
  obtain ⟨hP, hy, hplo, hlohi, hblo, hbb, -⟩ := hI
  haveI := hP
  have hb : 0 < I.b := lt_of_lt_of_le hblo hbb
  have hq0 : 0 < q := lt_of_lt_of_le hplo hq.1
  set l := lam I with hl
  set m := min l (I.b * I.phi) with hm
  have hξAmb : I.μξ ∈ Amb I := ⟨hP, fun _ _ => rfl⟩
  set f : ℝ → ℝ := fun ξ => min (ξ - I.b * q) I.y with hf
  have hfint : ∀ μ ∈ Amb I, Integrable f μ := fun μ hμ => by
    haveI : IsProbabilityMeasure μ := hμ.1
    exact integrable_min' μ m _ _ (hlower μ hμ)
  have hRF : ∀ μ, RF I μ q = q * ∫ ξ, f ξ ∂μ := fun μ => rfl
  set A := ∫ ξ in Iio l, f ξ ∂I.μξ with hA
  -- the value of `RF` and the bounds, for both cases
  have key : (q < pTilde I → ∀ μ ∈ Amb I, RF I μ q = RF I I.μξ q) ∧
      (¬ q < pTilde I → (∀ μ ∈ Amb I, R2 I q ≤ RF I μ q ∧ RF I μ q ≤ R1 I q) ∧
        RF I (witness I (I.y + I.b * q)) q = R1 I q ∧ RF I (witness I l) q = R2 I q) := by
    have hJconst : ∀ μ ∈ Amb I, ∀ c : ℝ, ∫ ξ in Ici l, c ∂μ = (1 - gam I) * c := by
      intro μ hμ c
      rw [setIntegral_const, real_Ici I hP μ hμ, smul_eq_mul]
    constructor
    · intro h
      have hc : I.y + I.b * q < l := by
        unfold pTilde at h
        rw [lt_div_iff₀ hb] at h; linarith [mul_comm q I.b]
      have hval : ∀ μ ∈ Amb I, ∫ ξ, f ξ ∂μ = A + (1 - gam I) * I.y := by
        intro μ hμ
        rw [split I μ hμ f (hfint μ hμ), ← hJconst μ hμ I.y]
        congr 1
        refine setIntegral_congr_fun measurableSet_Ici (fun ξ hξ => ?_)
        have : l ≤ ξ := hξ
        exact min_eq_right (by linarith)
      intro μ hμ
      rw [hRF, hRF, hval μ hμ, hval _ hξAmb]
    · intro h
      have hc : l ≤ I.y + I.b * q := by
        unfold pTilde at h; push_neg at h
        rw [div_le_iff₀ hb] at h; linarith
      set g : ℝ → ℝ := fun ξ => min ξ l with hg
      have hgint : Integrable g I.μξ := by
        have := integrable_min' I.μξ m 0 l (hlower _ hξAmb)
        simpa using this
      set B := ∫ ξ in Iio l, g ξ ∂I.μξ with hB
      have hE : ∫ ξ, min ξ (lam I) ∂I.μξ = B + (1 - gam I) * l := by
        have := split I I.μξ hξAmb g hgint
        rw [show (∫ ξ, min ξ (lam I) ∂I.μξ) = ∫ ξ, g ξ ∂I.μξ from rfl, this,
          ← hJconst _ hξAmb l]
        congr 1
        refine setIntegral_congr_fun measurableSet_Ici (fun ξ hξ => ?_)
        exact min_eq_right hξ
      have hAB : A = B - gam I * (I.b * q) := by
        rw [hA, hB]
        have h1 : ∫ ξ in Iio l, f ξ ∂I.μξ = ∫ ξ in Iio l, (g ξ - I.b * q) ∂I.μξ := by
          refine setIntegral_congr_fun measurableSet_Iio (fun ξ hξ => ?_)
          have : ξ < l := hξ
          simp only [hf, hg]
          rw [min_eq_left (by linarith), min_eq_left this.le]
        rw [h1, integral_sub hgint.integrableOn (integrable_const _).integrableOn,
          setIntegral_const, smul_eq_mul]
        rfl
      have hbounds : ∀ μ ∈ Amb I, (1 - gam I) * (l - I.b * q) ≤ ∫ ξ in Ici l, f ξ ∂μ ∧
          ∫ ξ in Ici l, f ξ ∂μ ≤ (1 - gam I) * I.y := by
        intro μ hμ
        haveI : IsProbabilityMeasure μ := hμ.1
        constructor
        · rw [← hJconst μ hμ]
          refine setIntegral_mono_on (integrable_const _).integrableOn (hfint μ hμ).integrableOn
            measurableSet_Ici (fun ξ hξ => ?_)
          have : l ≤ ξ := hξ
          exact le_min (by linarith) (by linarith)
        · rw [← hJconst μ hμ]
          exact setIntegral_mono_on (hfint μ hμ).integrableOn (integrable_const _).integrableOn
            measurableSet_Ici (fun ξ _ => min_le_right _ _)
      have hR1 : R1 I q = q * (A + (1 - gam I) * I.y) := by
        unfold R1; rw [hE, hAB]; ring
      have hR2 : R2 I q = q * (A + (1 - gam I) * (l - I.b * q)) := by
        unfold R2; rw [hE, hAB]; ring
      refine ⟨fun μ hμ => ?_, ?_, ?_⟩
      · have e : ∫ ξ, f ξ ∂μ = A + ∫ ξ in Ici l, f ξ ∂μ := split I μ hμ f (hfint μ hμ)
        rw [hRF, e, hR1, hR2]
        obtain ⟨h1, h2⟩ := hbounds μ hμ
        constructor
        · exact mul_le_mul_of_nonneg_left (by linarith) hq0.le
        · exact mul_le_mul_of_nonneg_left (by linarith) hq0.le
      · rw [hRF, integral_witness I hP _ f (hfint _ hξAmb), hR1]
        congr 2
        simp only [hf]
        rw [show I.y + I.b * q - I.b * q = I.y by ring, min_self]
      · rw [hRF, integral_witness I hP _ f (hfint _ hξAmb), hR2]
        congr 2
        simp only [hf]
        have hc' : lam I ≤ I.y + I.b * q := hc
        rw [min_eq_left]
        linarith
  have hS1 : IsGreatest ((fun μ => RF I μ q) '' Amb I)
      (if q < pTilde I then RF I I.μξ q else R1 I q) := by
    split_ifs with h
    · refine ⟨⟨I.μξ, hξAmb, rfl⟩, ?_⟩
      rintro _ ⟨μ, hμ, rfl⟩
      exact (key.1 h μ hμ).le
    · have hc : l ≤ I.y + I.b * q := by
        unfold pTilde at h; push_neg at h
        rw [div_le_iff₀ hb] at h; linarith
      refine ⟨⟨_, witness_mem I hP _ hc, (key.2 h).2.1⟩, ?_⟩
      rintro _ ⟨μ, hμ, rfl⟩
      exact ((key.2 h).1 μ hμ).2
  have hS2 : IsLeast ((fun μ => RF I μ q) '' Amb I)
      (if q < pTilde I then RF I I.μξ q else R2 I q) := by
    split_ifs with h
    · refine ⟨⟨I.μξ, hξAmb, rfl⟩, ?_⟩
      rintro _ ⟨μ, hμ, rfl⟩
      exact (key.1 h μ hμ).ge
    · refine ⟨⟨_, witness_mem I hP _ le_rfl, (key.2 h).2.2⟩, ?_⟩
      rintro _ ⟨μ, hμ, rfl⟩
      exact ((key.2 h).1 μ hμ).1
  exact ⟨hS1, hS2, hS1.csSup_eq, hS2.csInf_eq⟩
