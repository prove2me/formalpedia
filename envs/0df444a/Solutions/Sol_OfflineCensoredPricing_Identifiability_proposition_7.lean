-- Prove2me | solution 1 for OfflineCensoredPricing.Identifiability.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T17:37:04.116519+00:00
-- url     : https://prove2.me/submissions/96bc382a-3da7-41ea-8da1-a28dca8c515d

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model
import Theorems.Thm_OfflineCensoredPricing_Identifiability_proposition_2

open MeasureTheory Set OfflineCensoredPricing.Identifiability

namespace OCPProp7Aux



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

section General

variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (b y m : ℝ)

/-- `G(q) = E[min(ξ − b q, y)]`. -/
noncomputable def G (q : ℝ) : ℝ := ∫ ξ, min (ξ - b * q) y ∂μ

variable {μ b y m}

lemma integrable_min (hm : ∀ᵐ ξ ∂μ, m ≤ ξ) (q : ℝ) :
    Integrable (fun ξ => min (ξ - b * q) y) μ := by
  refine Integrable.of_bound (by fun_prop) (|y| + |m - b * q|) ?_
  filter_upwards [hm] with ξ hξ
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have : min (m - b * q) y ≤ min (ξ - b * q) y := min_le_min_right _ (by linarith)
    have h1 : -(|y| + |m - b * q|) ≤ min (m - b * q) y := by
      rcases min_cases (m - b * q) y with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
        linarith [neg_abs_le y, neg_abs_le (m - b * q), abs_nonneg y, abs_nonneg (m - b * q)]
    linarith
  · linarith [min_le_right (ξ - b * q) y, le_abs_self y, abs_nonneg (m - b * q)]

lemma G_lip (hb : 0 ≤ b) (hm : ∀ᵐ ξ ∂μ, m ≤ ξ) (q q' : ℝ) :
    |G μ b y q - G μ b y q'| ≤ b * |q - q'| := by
  unfold G
  rw [← integral_sub (integrable_min hm q) (integrable_min hm q')]
  have := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun ξ => min (ξ - b * q) y - min (ξ - b * q') y) (C := b * |q - q'|)
    (Filter.Eventually.of_forall (fun ξ => by
      rw [Real.norm_eq_abs]
      refine le_trans (abs_min_sub_min_le_max _ _ _ _) ?_
      rw [sub_self, abs_zero]
      refine max_le ?_ (by positivity)
      rw [show ξ - b * q - (ξ - b * q') = b * (q' - q) by ring, abs_mul, abs_of_nonneg hb,
        abs_sub_comm]))
  simpa [probReal_univ] using this

lemma G_cont (hb : 0 ≤ b) (hm : ∀ᵐ ξ ∂μ, m ≤ ξ) : Continuous (G μ b y) := by
  rw [Metric.continuous_iff]
  intro q ε hε
  refine ⟨ε / (b + 1), by positivity, fun q' hq' => ?_⟩
  rw [Real.dist_eq] at hq' ⊢
  have h := G_lip (y := y) hb hm q' q
  have h2 : b * |q' - q| ≤ b * (ε / (b + 1)) := mul_le_mul_of_nonneg_left hq'.le hb
  have h3 : b * (ε / (b + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

end General


lemma witness_vals {K : ℕ} (I : Instance K) (hI : I.Standing) (q : ℝ) (hq : q ∈ Icc I.plo I.phi)
    (hqt : ¬ q < pTilde I) :
    (∀ c, I.y + I.b * q ≤ c → RF I (witness I c) q = R1 I q) ∧
      RF I (witness I (lam I)) q = R2 I q := by
  have hlower := ae_lower I hI
  obtain ⟨hP, hy, hplo, hlohi, hblo, hbb, -⟩ := hI
  haveI := hP
  have hb : 0 < I.b := lt_of_lt_of_le hblo hbb
  set l := lam I with hl
  set m := min l (I.b * I.phi) with hm
  have hξAmb : I.μξ ∈ Amb I := ⟨hP, fun _ _ => rfl⟩
  set f : ℝ → ℝ := fun ξ => min (ξ - I.b * q) I.y with hf
  have hfint : Integrable f I.μξ := integrable_min' I.μξ m _ _ (hlower _ hξAmb)
  have hRF : ∀ μ, RF I μ q = q * ∫ ξ, f ξ ∂μ := fun μ => rfl
  set A := ∫ ξ in Iio l, f ξ ∂I.μξ with hA
  have hJconst : ∀ μ ∈ Amb I, ∀ c : ℝ, ∫ ξ in Ici l, c ∂μ = (1 - gam I) * c := by
    intro μ hμ c
    rw [setIntegral_const, real_Ici I hP μ hμ, smul_eq_mul]
  have hc : l ≤ I.y + I.b * q := by
    unfold pTilde at hqt; push_neg at hqt
    rw [div_le_iff₀ hb] at hqt; linarith
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
  have hR1 : R1 I q = q * (A + (1 - gam I) * I.y) := by
    unfold R1; rw [hE, hAB]; ring
  have hR2 : R2 I q = q * (A + (1 - gam I) * (l - I.b * q)) := by
    unfold R2; rw [hE, hAB]; ring
  refine ⟨fun c hc' => ?_, ?_⟩
  · rw [hRF, integral_witness I hP _ f hfint, hR1]
    congr 2
    simp only [hf]
    rw [min_eq_right (by linarith)]
  · rw [hRF, integral_witness I hP _ f hfint, hR2]
    congr 2
    simp only [hf]
    have hc' : lam I ≤ I.y + I.b * q := hc
    rw [min_eq_left]
    linarith

lemma RF_cont {K : ℕ} (I : Instance K) (hI : I.Standing) (μ : Measure ℝ) (hμ : μ ∈ Amb I) :
    Continuous (RF I μ) := by
  haveI : IsProbabilityMeasure μ := hμ.1
  have hb : 0 < I.b := lt_of_lt_of_le hI.2.2.2.2.1 hI.2.2.2.2.2.1
  exact continuous_id.mul (G_cont (y := I.y) hb.le (ae_lower I hI μ hμ))

lemma argmax_isGreatest (lo hi : ℝ) (R : ℝ → ℝ) (hc : Continuous R) (hlohi : lo ≤ hi) :
    IsGreatest {q ∈ Icc lo hi | ∀ q' ∈ Icc lo hi, R q' ≤ R q} (argmaxIcc lo hi R) := by
  set M := {q ∈ Icc lo hi | ∀ q' ∈ Icc lo hi, R q' ≤ R q} with hM
  obtain ⟨m0, hm0, hm0max⟩ := (isCompact_Icc (a := lo) (b := hi)).exists_isMaxOn
    ⟨lo, le_rfl, hlohi⟩ hc.continuousOn
  have hm0M : m0 ∈ M := ⟨hm0, fun q' hq' => hm0max hq'⟩
  have hbdd : BddAbove M := ⟨hi, fun q hq => hq.1.2⟩
  have hclosed : IsClosed M := by
    have : M = Icc lo hi ∩ ⋂ q' ∈ Icc lo hi, {q | R q' ≤ R q} := by
      ext q; simp [hM]
    rw [this]
    exact isClosed_Icc.inter (isClosed_biInter (fun q' _ => isClosed_le continuous_const hc))
  exact ⟨hclosed.csSup_mem ⟨m0, hm0M⟩ hbdd, fun q hq => le_csSup hbdd hq⟩

lemma argmax_congr (lo hi : ℝ) (f g : ℝ → ℝ) (h : ∀ q ∈ Icc lo hi, f q = g q) :
    {q ∈ Icc lo hi | ∀ q' ∈ Icc lo hi, f q' ≤ f q} =
      {q ∈ Icc lo hi | ∀ q' ∈ Icc lo hi, g q' ≤ g q} := by
  ext q
  constructor
  · rintro ⟨hq, hq2⟩; exact ⟨hq, fun q' hq' => by rw [← h q hq, ← h q' hq']; exact hq2 q' hq'⟩
  · rintro ⟨hq, hq2⟩; exact ⟨hq, fun q' hq' => by rw [h q hq, h q' hq']; exact hq2 q' hq'⟩


/-- Decomposition of `R_F(q)` for `q ≥ p̃` (Appendix C.1). -/
lemma RF_decomp {K : ℕ} (I : Instance K) (hI : I.Standing) (μ : Measure ℝ) (hμ : μ ∈ Amb I)
    (q : ℝ) (hqt : ¬ q < pTilde I) :
    RF I μ q = q * (∫ ξ in Iio (lam I), min (ξ - I.b * q) I.y ∂I.μξ +
        ∫ ξ in Ici (lam I), min (ξ - I.b * q) I.y ∂μ) ∧
      R1 I q = q * (∫ ξ in Iio (lam I), min (ξ - I.b * q) I.y ∂I.μξ + (1 - gam I) * I.y) ∧
      R2 I q = q * (∫ ξ in Iio (lam I), min (ξ - I.b * q) I.y ∂I.μξ +
        (1 - gam I) * (lam I - I.b * q)) := by
  have hlower := ae_lower I hI
  obtain ⟨hP, hy, hplo, hlohi, hblo, hbb, -⟩ := hI
  haveI := hP
  haveI : IsProbabilityMeasure μ := hμ.1
  have hb : 0 < I.b := lt_of_lt_of_le hblo hbb
  set l := lam I with hl
  set m := min l (I.b * I.phi) with hm
  have hξAmb : I.μξ ∈ Amb I := ⟨hP, fun _ _ => rfl⟩
  set f : ℝ → ℝ := fun ξ => min (ξ - I.b * q) I.y with hf
  have hfint : Integrable f I.μξ := integrable_min' I.μξ m _ _ (hlower _ hξAmb)
  set A := ∫ ξ in Iio l, f ξ ∂I.μξ with hA
  have hJconst : ∀ μ ∈ Amb I, ∀ c : ℝ, ∫ ξ in Ici l, c ∂μ = (1 - gam I) * c := by
    intro μ hμ c
    rw [setIntegral_const, real_Ici I hP μ hμ, smul_eq_mul]
  have hc : l ≤ I.y + I.b * q := by
    unfold pTilde at hqt; push_neg at hqt
    rw [div_le_iff₀ hb] at hqt; linarith
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
  refine ⟨?_, ?_, ?_⟩
  · show q * ∫ ξ, f ξ ∂μ = _
    rw [split I μ hμ f (integrable_min' μ m _ _ (hlower μ hμ))]
  · unfold R1; rw [hE, hAB]; ring
  · unfold R2; rw [hE, hAB]; ring

/-- (D.18): for `p̃ ≤ p₁ ≤ p₂`, `R_F(p₂) − R_F(p₁) ≤ R₁(p₂) − R₁(p₁)`. -/
lemma D18 {K : ℕ} (I : Instance K) (hI : I.Standing) (μ : Measure ℝ) (hμ : μ ∈ Amb I)
    (p1 p2 : ℝ) (h0 : 0 ≤ p1) (h1t : ¬ p1 < pTilde I) (h12 : p1 ≤ p2) :
    RF I μ p2 - RF I μ p1 ≤ R1 I p2 - R1 I p1 := by
  have h2t : ¬ p2 < pTilde I := fun h => h1t (lt_of_le_of_lt h12 h)
  obtain ⟨e1, e2, -⟩ := RF_decomp I hI μ hμ p1 h1t
  obtain ⟨e3, e4, -⟩ := RF_decomp I hI μ hμ p2 h2t
  rw [e1, e2, e3, e4]
  have hm := ae_lower I hI μ hμ
  haveI : IsProbabilityMeasure μ := hμ.1
  have hJ : ∀ c : ℝ, ∫ ξ in Ici (lam I), c ∂μ = (1 - gam I) * c := by
    intro c; rw [setIntegral_const, real_Ici I hI.1 μ hμ, smul_eq_mul]
  have key : ∫ ξ in Ici (lam I), p2 * (min (ξ - I.b * p2) I.y - I.y) ∂μ ≤
      ∫ ξ in Ici (lam I), p1 * (min (ξ - I.b * p1) I.y - I.y) ∂μ := by
    refine setIntegral_mono_on ((((integrable_min' μ _ _ _ hm).sub (integrable_const _)).const_mul
      _).integrableOn) ((((integrable_min' μ _ _ _ hm).sub (integrable_const _)).const_mul
      _).integrableOn) measurableSet_Ici (fun ξ _ => ?_)
    have hb : 0 < I.b := lt_of_lt_of_le hI.2.2.2.2.1 hI.2.2.2.2.2.1
    have u1 : min (ξ - I.b * p1) I.y - I.y ≤ 0 := by linarith [min_le_right (ξ - I.b * p1) I.y]
    have u12 : min (ξ - I.b * p2) I.y ≤ min (ξ - I.b * p1) I.y :=
      min_le_min_right _ (by nlinarith)
    nlinarith
  rw [integral_const_mul, integral_const_mul, integral_sub
    (integrable_min' μ _ _ _ hm).integrableOn (integrable_const _).integrableOn,
    integral_sub (integrable_min' μ _ _ _ hm).integrableOn (integrable_const _).integrableOn,
    hJ] at key
  nlinarith

/-- (D.19): for `p̃ ≤ p₁ ≤ p₂`, `R_F(p₁) − R_F(p₂) ≤ R₂(p₁) − R₂(p₂)`. -/
lemma D19 {K : ℕ} (I : Instance K) (hI : I.Standing) (μ : Measure ℝ) (hμ : μ ∈ Amb I)
    (p1 p2 : ℝ) (h0 : 0 ≤ p1) (h1t : ¬ p1 < pTilde I) (h12 : p1 ≤ p2) :
    RF I μ p1 - RF I μ p2 ≤ R2 I p1 - R2 I p2 := by
  have h2t : ¬ p2 < pTilde I := fun h => h1t (lt_of_le_of_lt h12 h)
  obtain ⟨e1, -, e2⟩ := RF_decomp I hI μ hμ p1 h1t
  obtain ⟨e3, -, e4⟩ := RF_decomp I hI μ hμ p2 h2t
  rw [e1, e2, e3, e4]
  have hm := ae_lower I hI μ hμ
  haveI : IsProbabilityMeasure μ := hμ.1
  have hb : 0 < I.b := lt_of_lt_of_le hI.2.2.2.2.1 hI.2.2.2.2.2.1
  have hc1 : lam I ≤ I.y + I.b * p1 := by
    unfold pTilde at h1t; push_neg at h1t
    rw [div_le_iff₀ hb] at h1t; linarith
  have hJ : ∀ c : ℝ, ∫ ξ in Ici (lam I), c ∂μ = (1 - gam I) * c := by
    intro c; rw [setIntegral_const, real_Ici I hI.1 μ hμ, smul_eq_mul]
  have key : ∫ ξ in Ici (lam I), p1 * (min (ξ - I.b * p1) I.y - (lam I - I.b * p1)) ∂μ ≤
      ∫ ξ in Ici (lam I), p2 * (min (ξ - I.b * p2) I.y - (lam I - I.b * p2)) ∂μ := by
    refine setIntegral_mono_on ((((integrable_min' μ _ _ _ hm).sub (integrable_const _)).const_mul
      _).integrableOn) ((((integrable_min' μ _ _ _ hm).sub (integrable_const _)).const_mul
      _).integrableOn) measurableSet_Ici (fun ξ hξ => ?_)
    have hξ' : lam I ≤ ξ := hξ
    have v1 : 0 ≤ min (ξ - I.b * p1) I.y - (lam I - I.b * p1) := by
      rcases min_cases (ξ - I.b * p1) I.y with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith
    have v12 : min (ξ - I.b * p1) I.y - (lam I - I.b * p1) ≤
        min (ξ - I.b * p2) I.y - (lam I - I.b * p2) := by
      have : min (ξ - I.b * p1) I.y + I.b * p1 ≤ min (ξ - I.b * p2) I.y + I.b * p2 := by
        rw [← min_add_add_right, ← min_add_add_right]
        exact min_le_min (by linarith) (by nlinarith)
      linarith
    nlinarith
  rw [integral_const_mul, integral_const_mul, integral_sub
    (integrable_min' μ _ _ _ hm).integrableOn (integrable_const _).integrableOn,
    integral_sub (integrable_min' μ _ _ _ hm).integrableOn (integrable_const _).integrableOn,
    hJ, hJ] at key
  nlinarith

end OCPProp7Aux

open OCPProp7Aux in
theorem solution {K : ℕ} (I : Instance K) (hI : I.Standing) (q : ℝ)
    (hq : q ∈ Icc I.plo I.phi) :
    IsGreatest ((fun μ => sSup (RF I μ '' Icc I.plo I.phi) - RF I μ q) '' Amb I)
        (max (Rmax I (pStarMax I) - Rmax I q) (Rmin I (pStarMin I) - Rmin I q)) ∧
      worstLoss I q =
        max (Rmax I (pStarMax I) - Rmax I q) (Rmin I (pStarMin I) - Rmin I q) := by
  have hI' := hI
  obtain ⟨hP, hy, hplo, hlohi, hblo, hbb, -⟩ := hI'
  haveI := hP
  have hb : 0 < I.b := lt_of_lt_of_le hblo hbb
  set c1 := max (lam I) (I.y + I.b * I.phi) with hc1
  have hF1 : witness I c1 ∈ Amb I := witness_mem I hP c1 (le_max_left _ _)
  have hF2 : witness I (lam I) ∈ Amb I := witness_mem I hP (lam I) le_rfl
  set Rx := RF I (witness I c1) with hRx
  set Rn := RF I (witness I (lam I)) with hRn
  have hP2 := fun q hq => proposition_2 I hI q hq
  have hRmax : ∀ q ∈ Icc I.plo I.phi, Rmax I q = Rx q := by
    intro q hq
    obtain ⟨hg, hl, hmax, -⟩ := hP2 q hq
    rw [hmax]
    split_ifs with h
    · rw [if_pos h] at hg hl
      exact le_antisymm (hl.2 ⟨_, hF1, rfl⟩) (hg.2 ⟨_, hF1, rfl⟩)
    · exact ((witness_vals I hI q hq h).1 c1
        (le_trans (by nlinarith [hq.2]) (le_max_right _ _))).symm
  have hRmin : ∀ q ∈ Icc I.plo I.phi, Rmin I q = Rn q := by
    intro q hq
    obtain ⟨hg, hl, -, hmin⟩ := hP2 q hq
    rw [hmin]
    split_ifs with h
    · rw [if_pos h] at hg hl
      exact le_antisymm (hl.2 ⟨_, hF2, rfl⟩) (hg.2 ⟨_, hF2, rfl⟩)
    · exact ((witness_vals I hI q hq h).2).symm
  -- `p*_max`, `p*_min` are maximizers
  have hpx : IsGreatest {q ∈ Icc I.plo I.phi | ∀ q' ∈ Icc I.plo I.phi, Rx q' ≤ Rx q}
      (pStarMax I) := by
    have := argmax_isGreatest I.plo I.phi Rx (RF_cont I hI _ hF1) hlohi.le
    unfold pStarMax argmaxIcc
    rw [argmax_congr _ _ _ _ hRmax]
    exact this
  have hpn : IsGreatest {q ∈ Icc I.plo I.phi | ∀ q' ∈ Icc I.plo I.phi, Rn q' ≤ Rn q}
      (pStarMin I) := by
    have := argmax_isGreatest I.plo I.phi Rn (RF_cont I hI _ hF2) hlohi.le
    unfold pStarMin argmaxIcc
    rw [argmax_congr _ _ _ _ hRmin]
    exact this
  -- maxima of a continuous revenue on `[p̲, p̄]`
  have hsup : ∀ μ ∈ Amb I, ∃ p' ∈ Icc I.plo I.phi,
      sSup (RF I μ '' Icc I.plo I.phi) = RF I μ p' := by
    intro μ hμ
    obtain ⟨p', hp', hmax⟩ := (isCompact_Icc (a := I.plo) (b := I.phi)).exists_isMaxOn
      ⟨I.plo, le_rfl, hlohi.le⟩ (RF_cont I hI μ hμ).continuousOn
    refine ⟨p', hp', IsGreatest.csSup_eq ⟨⟨p', hp', rfl⟩, ?_⟩⟩
    rintro _ ⟨r, hr, rfl⟩
    exact hmax hr
  set V := max (Rmax I (pStarMax I) - Rmax I q) (Rmin I (pStarMin I) - Rmin I q) with hV
  -- values of `R_F` versus `R_max`, `R_min`
  have below : ∀ μ ∈ Amb I, ∀ p ∈ Icc I.plo I.phi, p < pTilde I →
      RF I μ p = Rmax I p ∧ RF I μ p = Rmin I p := by
    intro μ hμ p hp h
    obtain ⟨hg, hl, hmax, hmin⟩ := hP2 p hp
    rw [if_pos h] at hg hl hmax hmin
    have e : RF I μ p = RF I I.μξ p := le_antisymm (hg.2 ⟨_, hμ, rfl⟩) (hl.2 ⟨_, hμ, rfl⟩)
    exact ⟨by rw [e, hmax], by rw [e, hmin]⟩
  have above : ∀ μ ∈ Amb I, ∀ p ∈ Icc I.plo I.phi, ¬ p < pTilde I →
      RF I μ p ≤ Rmax I p ∧ Rmin I p ≤ RF I μ p ∧ Rmax I p = R1 I p ∧ Rmin I p = R2 I p := by
    intro μ hμ p hp h
    obtain ⟨hg, hl, hmax, hmin⟩ := hP2 p hp
    rw [if_neg h] at hg hl hmax hmin
    exact ⟨by rw [hmax]; exact hg.2 ⟨_, hμ, rfl⟩, by rw [hmin]; exact hl.2 ⟨_, hμ, rfl⟩,
      hmax, hmin⟩
  have hxmax : ∀ p ∈ Icc I.plo I.phi, Rmax I p ≤ Rmax I (pStarMax I) := by
    intro p hp; rw [hRmax p hp, hRmax _ hpx.1.1]; exact hpx.1.2 p hp
  have hnmax : ∀ p ∈ Icc I.plo I.phi, Rmin I p ≤ Rmin I (pStarMin I) := by
    intro p hp; rw [hRmin p hp, hRmin _ hpn.1.1]; exact hpn.1.2 p hp
  have hub : ∀ μ ∈ Amb I, sSup (RF I μ '' Icc I.plo I.phi) - RF I μ q ≤ V := by
    intro μ hμ
    obtain ⟨p', hp', hs⟩ := hsup μ hμ
    rw [hs]
    have hp'0 : 0 ≤ p' := le_trans hplo.le hp'.1
    have hq0 : 0 ≤ q := le_trans hplo.le hq.1
    by_cases hqt : q < pTilde I
    · obtain ⟨eq1, -⟩ := below μ hμ q hq hqt
      by_cases hpt : p' < pTilde I
      · obtain ⟨ep1, -⟩ := below μ hμ p' hp' hpt
        rw [eq1, ep1]
        exact le_trans (by linarith [hxmax p' hp']) (le_max_left _ _)
      · obtain ⟨u, -⟩ := above μ hμ p' hp' hpt
        rw [eq1]
        exact le_trans (by linarith [hxmax p' hp']) (le_max_left _ _)
    · obtain ⟨-, lq, eq1, eq2⟩ := above μ hμ q hq hqt
      by_cases hpt : p' < pTilde I
      · obtain ⟨-, ep2⟩ := below μ hμ p' hp' hpt
        rw [ep2]
        exact le_trans (by linarith [hnmax p' hp']) (le_max_right _ _)
      · obtain ⟨-, -, ep1, ep2⟩ := above μ hμ p' hp' hpt
        rcases le_total q p' with h | h
        · have := D18 I hI μ hμ q p' hq0 hqt h
          rw [← eq1, ← ep1] at this
          exact le_trans (by linarith [hxmax p' hp']) (le_max_left _ _)
        · have := D19 I hI μ hμ p' q hp'0 hpt h
          rw [← eq2, ← ep2] at this
          exact le_trans (by linarith [hnmax p' hp']) (le_max_right _ _)
  have hmem : V ∈ (fun μ => sSup (RF I μ '' Icc I.plo I.phi) - RF I μ q) '' Amb I := by
    have sx : sSup (Rx '' Icc I.plo I.phi) = Rx (pStarMax I) :=
      IsGreatest.csSup_eq ⟨⟨_, hpx.1.1, rfl⟩, by rintro _ ⟨r, hr, rfl⟩; exact hpx.1.2 r hr⟩
    have sn : sSup (Rn '' Icc I.plo I.phi) = Rn (pStarMin I) :=
      IsGreatest.csSup_eq ⟨⟨_, hpn.1.1, rfl⟩, by rintro _ ⟨r, hr, rfl⟩; exact hpn.1.2 r hr⟩
    rcases le_total (Rmin I (pStarMin I) - Rmin I q) (Rmax I (pStarMax I) - Rmax I q) with h | h
    · refine ⟨_, hF1, ?_⟩
      simp only
      rw [hV, max_eq_left h, sx, hRmax _ hpx.1.1, hRmax q hq]
    · refine ⟨_, hF2, ?_⟩
      simp only
      rw [hV, max_eq_right h, sn, hRmin _ hpn.1.1, hRmin q hq]
  have hG : IsGreatest ((fun μ => sSup (RF I μ '' Icc I.plo I.phi) - RF I μ q) '' Amb I) V :=
    ⟨hmem, by rintro _ ⟨μ, hμ, rfl⟩; exact hub μ hμ⟩
  exact ⟨hG, hG.csSup_eq⟩
