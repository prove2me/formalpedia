-- Prove2me | solution 1 for OfflineCensoredPricing.Identifiability.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T17:33:04.361077+00:00
-- url     : https://prove2.me/submissions/49756ce8-0127-4286-a6cb-fba7129337d5

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model
import Theorems.Thm_OfflineCensoredPricing_Identifiability_proposition_1
import Theorems.Thm_OfflineCensoredPricing_Identifiability_proposition_2
import Theorems.Thm_OfflineCensoredPricing_Identifiability_proposition_7

open MeasureTheory Set OfflineCensoredPricing.Identifiability

namespace OCPProp6Aux


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


lemma concave_three' {lo hi : ℝ} (R : ℝ → ℝ) (hconc : ConcaveOn ℝ (Icc lo hi) R) (u v w : ℝ)
    (hu : u ∈ Icc lo hi) (hw : w ∈ Icc lo hi)
    (huv : u ≤ v) (hvw : v ≤ w) (huw : u < w) :
    (w - v) * R u + (v - u) * R w ≤ (w - u) * R v := by
  have hwu : 0 < w - u := by linarith
  have hne : w - u ≠ 0 := hwu.ne'
  have h := hconc.2 hu hw
    (show 0 ≤ (w - v) / (w - u) from div_nonneg (by linarith) hwu.le)
    (show 0 ≤ (v - u) / (w - u) from div_nonneg (by linarith) hwu.le)
    (by field_simp; ring)
  have hv : (w - v) / (w - u) * u + (v - u) / (w - u) * w = v := by
    field_simp; ring
  simp only [smul_eq_mul] at h
  rw [hv] at h
  have h2 := mul_le_mul_of_nonneg_left h hwu.le
  have e : (w - u) * ((w - v) / (w - u) * R u + (v - u) / (w - u) * R w) =
      (w - v) * R u + (v - u) * R w := by field_simp
  linarith

/-- A concave quadratic maximized at the right end `z` of `[u, z]` drops at least `a (z − q)²`
to the left of `z`. -/
lemma quad_left (a α u z : ℝ) (ha : 0 < a) (huz : u < z)
    (hmax : ∀ q ∈ Icc u z, q * (-a * q + α) ≤ z * (-a * z + α)) :
    ∀ q ≤ z, a * (z - q) ^ 2 ≤ z * (-a * z + α) - q * (-a * q + α) := by
  have hα : 2 * a * z ≤ α := by
    by_contra h
    push_neg at h
    set q1 := max u (α / (2 * a)) with hq1
    have hq1u : u ≤ q1 := le_max_left _ _
    have hq1a : α / (2 * a) ≤ q1 := le_max_right _ _
    have h2a : α / (2 * a) < z := by rw [div_lt_iff₀ (by linarith)]; linarith
    have hq1z : q1 < z := max_lt huz h2a
    have hm := hmax q1 ⟨hq1u, hq1z.le⟩
    have : α ≤ 2 * a * q1 := by
      have := (div_le_iff₀ (by linarith : (0:ℝ) < 2 * a)).1 hq1a; linarith
    nlinarith
  intro q hq
  nlinarith [mul_nonneg (sub_nonneg.2 hq) (sub_nonneg.2 hα)]

/-- Mirror image: maximized at the left end `z` of `[z, w]`, the drop to the right is at least
`a (q − z)²`. -/
lemma quad_right (a α z w : ℝ) (ha : 0 < a) (hzw : z < w)
    (hmax : ∀ q ∈ Icc z w, q * (-a * q + α) ≤ z * (-a * z + α)) :
    ∀ q, z ≤ q → a * (q - z) ^ 2 ≤ z * (-a * z + α) - q * (-a * q + α) := by
  have hα : α ≤ 2 * a * z := by
    by_contra h
    push_neg at h
    set q1 := min w (α / (2 * a)) with hq1
    have hq1w : q1 ≤ w := min_le_left _ _
    have hq1a : q1 ≤ α / (2 * a) := min_le_right _ _
    have h2a : z < α / (2 * a) := by rw [lt_div_iff₀ (by linarith)]; linarith
    have hq1z : z < q1 := lt_min hzw h2a
    have hm := hmax q1 ⟨hq1z.le, hq1w⟩
    have : 2 * a * q1 ≤ α := by
      have := (le_div_iff₀ (by linarith : (0:ℝ) < 2 * a)).1 hq1a; linarith
    nlinarith
  intro q hq
  nlinarith [mul_nonneg (sub_nonneg.2 hq) (sub_nonneg.2 hα)]

/-- `max (γ b s², b t²) ≥ γ b (s + t)² / (√γ + 1)²`. -/
lemma final_alg (γ b s t : ℝ) (hγ : 0 < γ) (hb : 0 < b) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    γ * b / (Real.sqrt γ + 1) ^ 2 * (s + t) ^ 2 ≤ max (γ * b * s ^ 2) (b * t ^ 2) := by
  set r := Real.sqrt γ with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg γ
  have hrr : r ^ 2 = γ := Real.sq_sqrt hγ.le
  have hpos : 0 < (r + 1) ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  rcases le_total t (r * s) with h | h
  · have h1 : r * (s + t) ≤ r * s * (r + 1) := by nlinarith
    have h2 : (r * (s + t)) ^ 2 ≤ (r * s * (r + 1)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have : γ * b * (s + t) ^ 2 ≤ γ * b * s ^ 2 * (r + 1) ^ 2 := by
      rw [← hrr]; nlinarith
    exact le_trans this (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le)
  · have h1 : r * (s + t) ≤ t * (r + 1) := by nlinarith
    have h2 : (r * (s + t)) ^ 2 ≤ (t * (r + 1)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have : γ * b * (s + t) ^ 2 ≤ b * t ^ 2 * (r + 1) ^ 2 := by
      rw [← hrr]; nlinarith
    exact le_trans this (mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le)

/-- The real-analysis core of Proposition 6 (Appendix C.6). `Rx`, `Rn` are concave on `[lo, hi]`,
agree left of `pt`, and are the quadratics `R₁`, `R₂` right of `pt`; `px`, `pn` are their largest
maximizers on `[lo, hi]`, assumed distinct. -/
lemma core (lo hi pt γ b E : ℝ) (Rx Rn : ℝ → ℝ) (hlo : 0 < lo) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hb : 0 < b)
    (hcx : ConcaveOn ℝ (Icc lo hi) Rx) (hcn : ConcaveOn ℝ (Icc lo hi) Rn)
    (heq : ∀ q ∈ Icc lo hi, q < pt → Rx q = Rn q)
    (h1 : ∀ q ∈ Icc lo hi, pt ≤ q → Rx q = q * (-(γ * b) * q + (E - (1 - γ) * b * pt)))
    (h2 : ∀ q ∈ Icc lo hi, pt ≤ q → Rn q = q * (-b * q + E))
    (px pn : ℝ)
    (hpx : IsGreatest {q ∈ Icc lo hi | ∀ q' ∈ Icc lo hi, Rx q' ≤ Rx q} px)
    (hpn : IsGreatest {q ∈ Icc lo hi | ∀ q' ∈ Icc lo hi, Rn q' ≤ Rn q} pn)
    (hne : px ≠ pn) :
    ∀ q ∈ Icc lo hi, γ * b / (Real.sqrt γ + 1) ^ 2 * (px - pn) ^ 2 ≤
      max (Rx px - Rx q) (Rn pn - Rn q) := by
  obtain ⟨⟨hpxI, hpxmax⟩, hpxub⟩ := hpx
  obtain ⟨⟨hpnI, hpnmax⟩, hpnub⟩ := hpn
  have sx : ∀ q ∈ Icc lo hi, px < q → Rx q < Rx px := by
    intro q hq hlt
    by_contra h; push_neg at h
    have : q ≤ px := hpxub ⟨hq, fun q' hq' => le_trans (hpxmax q' hq') h⟩
    linarith
  have sn : ∀ q ∈ Icc lo hi, pn < q → Rn q < Rn pn := by
    intro q hq hlt
    by_contra h; push_neg at h
    have : q ≤ pn := hpnub ⟨hq, fun q' hq' => le_trans (hpnmax q' hq') h⟩
    linarith
  -- Step 1: `pn < px`
  have hord : pn < px := by
    rcases lt_or_gt_of_ne hne with h | h
    · exfalso
      have a1 := sx pn hpnI h
      have a2 := hpnmax px hpxI
      by_cases hpn' : pn < pt
      · have := heq pn hpnI hpn'; have := heq px hpxI (by linarith); linarith
      · push_neg at hpn'
        have e1 := h1 pn hpnI hpn'; have e2 := h2 pn hpnI hpn'
        by_cases hpx' : px < pt
        · have := heq px hpxI hpx'
          have : 0 ≤ (1 - γ) * b * pn * (pn - pt) := by
            have := hpnI.1; apply mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hb.le)
              (by linarith)) (by linarith)
          nlinarith
        · push_neg at hpx'
          have e3 := h1 px hpxI hpx'; have e4 := h2 px hpxI hpx'
          have hlx : 0 < px := lt_of_lt_of_le hlo hpxI.1
          have : (1 - γ) * b * px * (px - pt) ≤ (1 - γ) * b * pn * (pn - pt) := by
            have hk : 0 ≤ (1 - γ) * b := mul_nonneg (by linarith) hb.le
            have : px * (px - pt) ≤ pn * (pn - pt) := by nlinarith
            nlinarith
          nlinarith
    · exact h
  -- Step 2: `pt ≤ pn`
  have hpt : pt ≤ pn := by
    by_contra hlt; push_neg at hlt
    have ii : ∀ q ∈ Icc lo hi, pn < q → Rx q < Rx pn := by
      intro q hq hq'
      by_cases hqt : q < pt
      · rw [heq q hq hqt, heq pn hpnI hlt]; exact sn q hq hq'
      · push_neg at hqt
        set q0 := (pn + pt) / 2 with hq0
        have hq0I : q0 ∈ Icc lo hi := ⟨by linarith [hpnI.1], by linarith [hq.2]⟩
        have hq0' : Rx q0 < Rx pn := by
          rw [heq q0 hq0I (by linarith), heq pn hpnI hlt]; exact sn q0 hq0I (by linarith)
        have c3 := concave_three' Rx hcx pn q0 q hpnI hq (by linarith) (by linarith)
          (by linarith)
        by_contra hge; push_neg at hge
        nlinarith
    have hgr : IsGreatest {q ∈ Icc lo hi | ∀ q' ∈ Icc lo hi, Rx q' ≤ Rx q} pn := by
      refine ⟨⟨hpnI, fun q' hq' => ?_⟩, fun q hq => ?_⟩
      · rcases le_or_gt q' pn with h | h
        · rw [heq q' hq' (by linarith), heq pn hpnI hlt]; exact hpnmax q' hq'
        · exact (ii q' hq' h).le
      · by_contra h; push_neg at h
        linarith [ii q hq.1 h, hq.2 pn hpnI]
    have hpx' : IsGreatest {q ∈ Icc lo hi | ∀ q' ∈ Icc lo hi, Rx q' ≤ Rx q} px :=
      ⟨⟨hpxI, hpxmax⟩, hpxub⟩
    exact hne (hpx'.unique hgr)
  -- Step 3: quadratic drops
  have hgb : 0 < γ * b := mul_pos hγ0 hb
  have QL := quad_left (γ * b) (E - (1 - γ) * b * pt) pn px hgb hord (fun q hq => by
    have hqI : q ∈ Icc lo hi := ⟨le_trans hpnI.1 hq.1, le_trans hq.2 hpxI.2⟩
    rw [← h1 q hqI (by linarith [hq.1]), ← h1 px hpxI (by linarith)]
    exact hpxmax q hqI)
  have QR := quad_right b E pn px hb hord (fun q hq => by
    have hqI : q ∈ Icc lo hi := ⟨le_trans hpnI.1 hq.1, le_trans hq.2 hpxI.2⟩
    rw [← h2 q hqI (by linarith [hq.1]), ← h2 pn hpnI hpt]
    exact hpnmax q hqI)
  have hr : 1 ≤ (Real.sqrt γ + 1) ^ 2 := by
    have := Real.sqrt_nonneg γ; nlinarith
  have hrγ : γ ≤ (Real.sqrt γ + 1) ^ 2 := by
    have := Real.sq_sqrt hγ0.le; have := Real.sqrt_nonneg γ; nlinarith
  set D := px - pn with hD
  have hcle1 : γ * b / (Real.sqrt γ + 1) ^ 2 * D ^ 2 ≤ γ * b * D ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    have h0 : 0 ≤ γ * b * D ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hr h0]
  have hcle2 : γ * b / (Real.sqrt γ + 1) ^ 2 * D ^ 2 ≤ b * D ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    have : 0 ≤ b * D ^ 2 := by positivity
    nlinarith
  intro q hq
  rcases le_or_gt q pn with hqn | hqn
  · -- left of `pn`
    have hRq : Rx q ≤ Rx pn := by
      rcases eq_or_lt_of_le hqn with h | h
      · rw [h]
      · have c3 := concave_three' Rx hcx q pn px hq hpxI h.le hord.le (by linarith)
        have := hpxmax q hq
        nlinarith
    have q1 := QL pn hord.le
    rw [← h1 pn hpnI hpt, ← h1 px hpxI (by linarith)] at q1
    exact le_trans hcle1 (le_trans (by linarith) (le_max_left _ _))
  · rcases le_or_gt q px with hqx | hqx
    · have qa := QL q hqx
      have qb := QR q hqn.le
      rw [← h1 q hq (by linarith), ← h1 px hpxI (by linarith)] at qa
      rw [← h2 q hq (by linarith), ← h2 pn hpnI hpt] at qb
      have hf := final_alg γ b (px - q) (q - pn) hγ0 hb (by linarith) (by linarith)
      rw [show px - q + (q - pn) = D by ring] at hf
      refine le_trans hf (max_le_max ?_ ?_) <;> linarith
    · have qb := QR q hqn.le
      rw [← h2 q hq (by linarith), ← h2 pn hpnI hpt] at qb
      have : b * D ^ 2 ≤ b * (q - pn) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hb.le
        apply pow_le_pow_left₀ (by linarith) (by linarith)
      exact le_trans hcle2 (le_trans (by linarith) (le_max_right _ _))


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

end OCPProp6Aux

open OCPProp6Aux in
theorem solution {K : ℕ} (I : Instance K) (hI : I.Standing) (hne : pStarMax I ≠ pStarMin I) :
    gam I * I.b / (Real.sqrt (gam I) + 1) ^ 2 * (pStarMax I - pStarMin I) ^ 2 ≤ Delta I ∧
      ∀ q ∈ Icc I.plo I.phi,
        gam I * I.b / (Real.sqrt (gam I) + 1) ^ 2 * (pStarMax I - pStarMin I) ^ 2 ≤
          worstLoss I q := by
  have hI' := hI
  obtain ⟨hP, hy, hplo, hlohi, hblo, hbb, hbhi, hK, -, hpi, hyh, -, hgam, -⟩ := hI'
  haveI := hP
  have hb : 0 < I.b := lt_of_lt_of_le hblo hbb
  -- `0 < γ ≤ 1`
  have hγ0 : 0 < gam I := by
    have i : Fin K := ⟨0, by omega⟩
    have hle : I.yh i + I.b * I.p i ≤ lam I :=
      le_ciSup (Finite.bddAbove_range (fun i => I.yh i + I.b * I.p i)) i
    exact lt_of_lt_of_le (hgam i) (measureReal_mono (Iio_subset_Iio hle))
  have hγ1 : gam I ≤ 1 := by unfold gam; exact measureReal_le_one
  -- the two extremal laws
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
  have heq : ∀ q ∈ Icc I.plo I.phi, q < pTilde I → Rx q = Rn q := by
    intro q hq h
    rw [← hRmax q hq, ← hRmin q hq, (hP2 q hq).2.2.1, (hP2 q hq).2.2.2, if_pos h, if_pos h]
  set E := ∫ ξ, min ξ (lam I) ∂I.μξ with hE
  have h1 : ∀ q ∈ Icc I.plo I.phi, pTilde I ≤ q →
      Rx q = q * (-(gam I * I.b) * q + (E - (1 - gam I) * I.b * pTilde I)) := by
    intro q hq h
    rw [← hRmax q hq, (hP2 q hq).2.2.1, if_neg (not_lt.2 h)]
    unfold R1 pTilde
    field_simp
    ring
  have h2 : ∀ q ∈ Icc I.plo I.phi, pTilde I ≤ q → Rn q = q * (-I.b * q + E) := by
    intro q hq h
    rw [← hRmin q hq, (hP2 q hq).2.2.2, if_neg (not_lt.2 h)]
    rfl
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
  have hcore := core I.plo I.phi (pTilde I) (gam I) I.b E Rx Rn hplo hγ0 hγ1 hb
    (proposition_1 I hI _ hF1).1 (proposition_1 I hI _ hF2).1 heq h1 h2
    (pStarMax I) (pStarMin I) hpx hpn hne
  have hwl : ∀ q ∈ Icc I.plo I.phi,
      gam I * I.b / (Real.sqrt (gam I) + 1) ^ 2 * (pStarMax I - pStarMin I) ^ 2 ≤
        worstLoss I q := by
    intro q hq
    rw [(proposition_7 I hI q hq).2, hRmax q hq, hRmin q hq, hRmax _ hpx.1.1,
      hRmin _ hpn.1.1]
    exact hcore q hq
  refine ⟨?_, hwl⟩
  unfold Delta
  refine le_csInf ⟨_, ⟨I.plo, ⟨le_rfl, hlohi.le⟩, rfl⟩⟩ ?_
  rintro _ ⟨q, hq, rfl⟩
  exact hwl q hq
