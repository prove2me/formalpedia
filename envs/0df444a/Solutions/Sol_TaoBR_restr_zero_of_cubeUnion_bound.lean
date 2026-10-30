-- Prove2me | solution 1 for TaoBR.restr_zero_of_cubeUnion_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:46:24.804221+00:00
-- url     : https://prove2.me/submissions/5eb92626-423a-4a3d-9ed6-44fd7b378738

import Definitions.Def_TaoBR
import Mathlib

section
section
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace

namespace TaoBR.CU

variable {n : ℕ}

/-- The indicator of a set, with value `1 : ℂ`. -/
noncomputable def ind (S : Set (E n)) : E n → ℂ := S.indicator fun _ => (1 : ℂ)

/-- The lattice point `k` as a point of `E n`. -/
noncomputable def latt (k : Fin n → ℤ) : E n := WithLp.toLp 2 (fun i => (k i : ℝ))

lemma latt_apply (k : Fin n → ℤ) (i : Fin n) : latt k i = (k i : ℝ) := rfl

/-- The `c`-cube as a box of `Fin n → ℝ`. -/
lemma cCube_eq (c : ℝ) (k : Fin n → ℤ) :
    cCube c k = (WithLp.ofLp : E n → (Fin n → ℝ)) ⁻¹'
      Set.pi Set.univ (fun i => Set.Icc ((k i : ℝ) - c / 2) (k i + c / 2)) := by
  ext x
  simp only [cCube, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  show (∀ i, |x i - k i| ≤ c / 2) ↔ _
  constructor
  · intro h i; have := abs_le.mp (h i); exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · intro h i; have := h i; exact abs_le.mpr ⟨by linarith [this.1], by linarith [this.2]⟩

lemma measurableSet_cCube (c : ℝ) (k : Fin n → ℤ) : MeasurableSet (cCube c k) := by
  rw [cCube_eq]
  exact (MeasurableSet.univ_pi fun i => measurableSet_Icc).preimage
    (WithLp.measurable_ofLp 2 _)

lemma volume_cCube {c : ℝ} (hc : 0 ≤ c) (k : Fin n → ℤ) :
    volume (cCube c k) = ENNReal.ofReal c ^ n := by
  rw [cCube_eq, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    ((MeasurableSet.univ_pi fun i => measurableSet_Icc).nullMeasurableSet), volume_pi,
    Measure.pi_pi]
  have : ∀ i : Fin n, ((k i : ℝ) + c / 2 - (k i - c / 2)) = c := fun i => by ring
  simp only [Real.volume_Icc, this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma volume_cCube_lt_top (c : ℝ) (k : Fin n → ℤ) : volume (cCube c k) < ⊤ := by
  have hsub : cCube c k ⊆ cCube |c| k := fun x hx i => (hx i).trans (by
    have := le_abs_self c; linarith)
  calc volume (cCube c k) ≤ volume (cCube |c| k) := measure_mono hsub
    _ < ⊤ := by rw [volume_cCube (abs_nonneg c)]; exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top

lemma cCube_disjoint {c : ℝ} (hc1 : c < 1) {k k' : Fin n → ℤ} (h : k ≠ k') :
    Disjoint (cCube c k) (cCube c k') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  have h1 := hx i
  have h2 := hx' i
  have : (1 : ℝ) ≤ |(k i : ℝ) - k' i| := by
    have : k i - k' i ≠ 0 := sub_ne_zero.mpr hi
    have h3 : (1 : ℤ) ≤ |k i - k' i| := Int.one_le_abs this
    exact_mod_cast h3
  have : |(k i : ℝ) - k' i| ≤ |x i - k i| + |x i - k' i| := by
    calc |(k i : ℝ) - k' i| = |(x i - k' i) - (x i - k i)| := by ring_nf
      _ ≤ |x i - k' i| + |x i - k i| := abs_sub _ _
      _ = _ := add_comm _ _
  linarith

lemma mem_cCube_iff_sub (c : ℝ) (k : Fin n → ℤ) (x : E n) :
    x ∈ cCube c k ↔ x - latt k ∈ cCube c 0 := by
  simp only [cCube, Set.mem_ofPred_eq, PiLp.sub_apply, latt_apply, Pi.zero_apply, Int.cast_zero,
    sub_zero]

/-- The Fourier transform of the indicator of the `c`-cube at `k`. -/
noncomputable def phi (c : ℝ) (k : Fin n → ℤ) (ω : E n) : ℂ := 𝓕 (ind (cCube c k)) ω

lemma integrable_ind_cCube (c : ℝ) (k : Fin n → ℤ) : Integrable (ind (cCube c k)) := by
  unfold ind
  exact (integrableOn_const (volume_cCube_lt_top c k).ne).integrable_indicator
    (measurableSet_cCube c k)

lemma norm_phi_le {c : ℝ} (hc : 0 ≤ c) (k : Fin n → ℤ) (ω : E n) : ‖phi c k ω‖ ≤ c ^ n := by
  unfold phi
  rw [fourier_eq]
  calc ‖∫ v, 𝐞 (-⟪v, ω⟫) • ind (cCube c k) v‖ ≤ ∫ v, ‖𝐞 (-⟪v, ω⟫) • ind (cCube c k) v‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ v, (cCube c k).indicator (fun _ => (1 : ℝ)) v := by
        congr 1; ext v
        by_cases hv : v ∈ cCube c k <;> simp [ind, Set.indicator, hv, Circle.norm_smul]
    _ = c ^ n := by
        rw [integral_indicator (measurableSet_cCube c k), setIntegral_const, smul_eq_mul, mul_one,
          measureReal_def, volume_cCube hc, ENNReal.toReal_pow, ENNReal.toReal_ofReal hc]

lemma phi_translate (c : ℝ) (k : Fin n → ℤ) (ω : E n) :
    phi c k ω = 𝐞 (-⟪latt k, ω⟫) • phi c 0 ω := by
  unfold phi
  rw [fourier_eq, fourier_eq]
  simp only [Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]
  rw [← integral_add_right_eq_self (μ := (volume : Measure (E n))) _ (latt k)]
  congr 1; ext v
  have hind : ind (cCube c k) (v + latt k) = ind (cCube c 0) v := by
    have : v + latt k ∈ cCube c k ↔ v ∈ cCube c 0 := by
      rw [mem_cCube_iff_sub c k, add_sub_cancel_right]
    by_cases hv : v ∈ cCube c 0
    · simp [ind, Set.indicator, hv, this.mpr hv]
    · simp [ind, Set.indicator, hv, mt this.mp hv]
  rw [hind, inner_add_left, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

lemma continuous_phi (c : ℝ) (k : Fin n → ℤ) : Continuous (phi c k) := by
  unfold phi
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by simpa using (continuous_inner : Continuous fun p : E n × E n => ⟪p.1, p.2⟫))
    (integrable_ind_cCube c k)

end TaoBR.CU

end
end

section
section
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace

namespace TaoBR.CU

variable {n : ℕ}

/-- The one-dimensional factor of the transform of the `c`-cube. -/
noncomputable def fac (c s : ℝ) : ℂ :=
  ∫ t in Set.Icc (-(c / 2)) (c / 2), ((𝐞 (-(t * s)) : ℂ))

lemma integral_cos_mul_sym {c s : ℝ} (hc : 0 < c) :
    ∫ t in Set.Icc (-(c / 2)) (c / 2), Real.cos (2 * π * s * t) =
      if s = 0 then c else Real.sin (π * c * s) / (π * s) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  split_ifs with hs
  · subst hs; simp
  · have hd : 2 * π * s ≠ 0 := by positivity
    rw [intervalIntegral.integral_comp_mul_left (fun t => Real.cos t) hd, integral_cos]
    rw [show 2 * π * s * (c / 2) = π * c * s by ring,
      show 2 * π * s * -(c / 2) = -(π * c * s) by ring, Real.sin_neg, smul_eq_mul]
    field_simp
    ring

lemma re_fac {c s : ℝ} (hc : 0 < c) :
    (fac c s).re = if s = 0 then c else Real.sin (π * c * s) / (π * s) := by
  rw [← integral_cos_mul_sym hc, fac, ← RCLike.re_eq_complex_re, ← integral_re]
  · congr 1; ext t
    rw [RCLike.re_eq_complex_re, Real.fourierChar_apply, Complex.exp_ofReal_mul_I_re]
    rw [show 2 * π * -(t * s) = -(2 * π * s * t) by ring, Real.cos_neg]
  · exact (Continuous.integrableOn_Icc (by fun_prop))

lemma re_fac_pos {c s : ℝ} (hc : 0 < c) (hc1 : c < 1) (hs : |s| ≤ 1) : 0 < (fac c s).re := by
  rw [re_fac hc]
  split_ifs with h0
  · exact hc
  · have key : Real.sin (π * c * s) / (π * s) = Real.sin (π * c * |s|) / (π * |s|) := by
      rcases le_or_gt 0 s with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, mul_neg, Real.sin_neg, mul_neg, neg_div_neg_eq]
    rw [key]
    have hs0 : 0 < |s| := abs_pos.mpr h0
    apply div_pos _ (by positivity)
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    calc π * c * |s| ≤ π * c * 1 := by gcongr
      _ < π := by nlinarith [Real.pi_pos]

lemma inner_toLp (y : Fin n → ℝ) (ω : E n) :
    ⟪(WithLp.toLp 2 y : E n), ω⟫ = ∑ i, y i * ω i := by
  simp [PiLp.inner_apply, mul_comm]

lemma phi_zero_eq_prod {c : ℝ} (ω : E n) : phi c 0 ω = ∏ i, fac c (ω i) := by
  unfold phi
  rw [fourier_eq, ← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  have : ∀ y : Fin n → ℝ, 𝐞 (-⟪(MeasurableEquiv.toLp 2 (Fin n → ℝ) y : E n), ω⟫) •
      ind (cCube c 0) (MeasurableEquiv.toLp 2 (Fin n → ℝ) y) =
      ∏ i, (Set.Icc (-(c / 2)) (c / 2)).indicator (fun t => ((𝐞 (-(t * ω i)) : ℂ))) (y i) := by
    intro y
    simp only [MeasurableEquiv.coe_toLp]
    rw [inner_toLp, Circle.smul_def, smul_eq_mul]
    by_cases hy : ∀ i, y i ∈ Set.Icc (-(c / 2)) (c / 2)
    · have hmem : (WithLp.toLp 2 y : E n) ∈ cCube c 0 := by
        intro i
        simp only [Pi.zero_apply, Int.cast_zero, sub_zero]
        exact abs_le.mpr (hy i)
      rw [ind, Set.indicator_of_mem hmem, mul_one]
      rw [Finset.prod_congr rfl (fun i _ => Set.indicator_of_mem (hy i) _)]
      simp only [Real.fourierChar_apply]
      rw [← Complex.exp_sum]
      congr 1
      push_cast
      rw [← Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
    · push_neg at hy
      obtain ⟨i, hi⟩ := hy
      have hnmem : (WithLp.toLp 2 y : E n) ∉ cCube c 0 := by
        intro h
        apply hi
        have := h i
        simp only [Pi.zero_apply, Int.cast_zero, sub_zero] at this
        exact abs_le.mp this
      rw [ind, Set.indicator_of_notMem hnmem, mul_zero]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
  calc _ = ∫ y : Fin n → ℝ, ∏ i, (Set.Icc (-(c / 2)) (c / 2)).indicator
        (fun t => ((𝐞 (-(t * ω i)) : ℂ))) (y i) := integral_congr_ae (Filter.Eventually.of_forall this)
    _ = _ := ?_
  rw [integral_fintype_prod_volume_eq_prod]
  congr 1; ext i
  rw [fac, integral_indicator measurableSet_Icc]

lemma phi_zero_ne_zero {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {ω : E n} (hω : ‖ω‖ ≤ 1) :
    phi c 0 ω ≠ 0 := by
  rw [phi_zero_eq_prod]
  rw [Finset.prod_ne_zero_iff]
  intro i _
  have hi : |ω i| ≤ 1 := by
    have := PiLp.norm_apply_le ω i
    simp only [Real.norm_eq_abs] at this
    linarith
  intro h0
  have := re_fac_pos hc hc1 hi
  rw [h0, Complex.zero_re] at this
  exact lt_irrefl _ this

lemma exists_lower_bound_phi {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    ∃ m : ℝ, 0 < m ∧ ∀ ω : E n, ‖ω‖ = 1 → m ≤ ‖phi c 0 ω‖ := by
  by_cases hne : (sphere (0 : E n) 1).Nonempty
  · obtain ⟨ω₀, hω₀, hmin⟩ := (isCompact_sphere (0 : E n) 1).exists_isMinOn hne
      (continuous_norm.comp (continuous_phi c 0)).continuousOn
    refine ⟨‖phi c 0 ω₀‖, ?_, ?_⟩
    · apply norm_pos_iff.mpr
      apply phi_zero_ne_zero hc hc1
      rw [mem_sphere_zero_iff_norm] at hω₀; exact hω₀.le
    · intro ω hω
      exact hmin (mem_sphere_zero_iff_norm.mpr hω)
  · refine ⟨1, one_pos, fun ω hω => ?_⟩
    exact absurd ⟨ω, mem_sphere_zero_iff_norm.mpr hω⟩ hne

end TaoBR.CU

end
end

section
section
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace

namespace TaoBR.CU

variable {n : ℕ}

/-- `∑ a_k φ_k` on the unit sphere: the restriction of a function constant on `c`-cubes. -/
noncomputable def cubeSum (c : ℝ) (s : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℂ)
    (ω : sphere (0 : E n) 1) : ℂ := ∑ k ∈ s, a k * phi c k ω

lemma continuous_cubeSum (c : ℝ) (s : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℂ) :
    Continuous (cubeSum c s a) := by
  unfold cubeSum
  exact continuous_finset_sum _ fun k _ =>
    continuous_const.mul ((continuous_phi c k).comp continuous_subtype_val)

lemma aesm_cubeSum (c : ℝ) (s : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℂ) :
    AEStronglyMeasurable (cubeSum c s a) (sphereMeasure n) :=
  (continuous_cubeSum c s a).aestronglyMeasurable

lemma cubeSum_add (c : ℝ) (s : Finset (Fin n → ℤ)) (a a' : (Fin n → ℤ) → ℂ) :
    cubeSum c s (fun k => a k + a' k) = cubeSum c s a + cubeSum c s a' := by
  funext ω; simp only [cubeSum, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma norm_cubeSum_le {c : ℝ} (hc : 0 ≤ c) (s : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℂ)
    (ω : sphere (0 : E n) 1) : ‖cubeSum c s a ω‖ ≤ ∑ k ∈ s, ‖a k‖ * c ^ n := by
  unfold cubeSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_phi_le hc k _) (norm_nonneg _)

lemma restriction_cubeFun (c : ℝ) (s : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℂ) :
    restriction (fun x => ∑ k ∈ s, a k * ind (cCube c k) x) = cubeSum c s a := by
  funext ω
  simp only [restriction, cubeSum, phi, fourier_eq, Finset.smul_sum]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_const_mul]
    congr 1; ext v
    simp only [Circle.smul_def, smul_eq_mul]
    try ring
  · intro k _
    have := (Real.fourierIntegral_convergent_iff (ω : E n)).2
      ((integrable_ind_cCube c k).const_mul (a k))
    refine this.congr (Filter.Eventually.of_forall fun v => ?_)
    simp only [Circle.smul_def, smul_eq_mul]
    try ring

lemma ind_iUnion_eq_sum {c : ℝ} (hc1 : c < 1) (t : Finset (Fin n → ℤ)) (x : E n) :
    (⋃ k ∈ t, cCube c k).indicator (fun _ => (1 : ℂ)) x = ∑ k ∈ t, 1 * ind (cCube c k) x := by
  by_cases hx : ∃ k ∈ t, x ∈ cCube c k
  · obtain ⟨k, hk, hxk⟩ := hx
    rw [Set.indicator_of_mem (Set.mem_iUnion₂.mpr ⟨k, hk, hxk⟩)]
    rw [Finset.sum_eq_single k]
    · simp [ind, hxk]
    · intro k' _ hk'
      have : x ∉ cCube c k' := fun h => Set.disjoint_left.mp (cCube_disjoint hc1 hk') h hxk
      simp [ind, this]
    · intro h; exact absurd hk h
  · simp only [not_exists, not_and] at hx
    rw [Set.indicator_of_notMem]
    · symm; apply Finset.sum_eq_zero; intro k hk; simp [ind, hx k hk]
    · simp only [Set.mem_iUnion]; rintro ⟨k, hk, h⟩; exact hx k hk h

lemma volume_iUnion_cCube {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1) (t : Finset (Fin n → ℤ)) :
    volume (⋃ k ∈ t, cCube c k) = t.card * ENNReal.ofReal c ^ n := by
  rw [measure_biUnion_finset (fun k _ k' _ hk => cCube_disjoint hc1 hk)
    (fun k _ => measurableSet_cCube c k)]
  simp [volume_cCube hc]

lemma restriction_iUnion {c : ℝ} (hc1 : c < 1) (t : Finset (Fin n → ℤ)) :
    restriction ((⋃ k ∈ t, cCube c k).indicator fun _ => (1 : ℂ)) = cubeSum c t (fun _ => 1) := by
  rw [← restriction_cubeFun]
  congr 1; funext x; exact ind_iUnion_eq_sum hc1 t x

/-! ### The Riemann sum bound -/

lemma bernoulli_step {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h)
    (hxh : h ≤ x) : h * x ^ (-a) ≤ (x ^ (1 - a) - (x - h) ^ (1 - a)) / (1 - a) := by
  have hr : 0 < 1 - a := by linarith
  rw [le_div_iff₀ hr]
  have hb := rpow_one_add_le_one_add_mul_self (s := -(h / x)) (p := 1 - a)
    (by rw [neg_le_neg_iff, div_le_one hx]; exact hxh) hr.le (by linarith)
  have h1 : 1 + -(h / x) = (x - h) / x := by field_simp; ring
  rw [h1, Real.div_rpow (by linarith) hx.le] at hb
  have hxr : 0 < x ^ (1 - a) := Real.rpow_pos_of_pos hx _
  rw [div_le_iff₀ hxr] at hb
  have hxa : x ^ (1 - a) = x * x ^ (-a) := by
    rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one]
  rw [hxa] at hb ⊢
  have : (1 + (1 - a) * -(h / x)) * (x * x ^ (-a)) = x * x ^ (-a) - (1 - a) * h * x ^ (-a) := by
    field_simp; ring
  rw [this] at hb
  nlinarith

lemma riemann_sum_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (L : ℕ) (hL : 1 ≤ L) :
    (1 / (L : ℝ)) * ∑ j ∈ Finset.range L, (((j : ℝ) + 1) / L) ^ (-a) ≤ 1 / (1 - a) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hstep : ∀ j ∈ Finset.range L, (1 / (L : ℝ)) * (((j : ℝ) + 1) / L) ^ (-a) ≤
      ((((j : ℝ) + 1) / L) ^ (1 - a) - ((j : ℝ) / L) ^ (1 - a)) / (1 - a) := by
    intro j _
    have := bernoulli_step ha0 ha1 (x := ((j : ℝ) + 1) / L) (h := 1 / L) (by positivity)
      (by positivity) (by gcongr; linarith)
    convert this using 3
    field_simp; ring
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
  rw [← Finset.sum_div]
  have := Finset.sum_range_sub (fun j : ℕ => ((j : ℝ) / L) ^ (1 - a)) L
  push_cast at this
  rw [this]
  simp only [Nat.cast_zero, zero_div]
  rw [div_self hL'.ne', Real.one_rpow, Real.zero_rpow (by linarith), sub_zero]

end TaoBR.CU

end
end

section
section
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace

namespace TaoBR.CU

variable {n : ℕ}

lemma eLpNorm_le_of_bound {G : sphere (0 : E n) 1 → ℂ} {B : ℝ} (q : ℝ≥0∞)
    (h : ∀ ω, ‖G ω‖ ≤ B) :
    eLpNorm G q (sphereMeasure n) ≤ sphereMeasure n Set.univ ^ q.toReal⁻¹ * ENNReal.ofReal B :=
  eLpNorm_le_of_ae_bound (Filter.Eventually.of_forall h)

lemma range_filter_card (L a : ℕ) (ha : a ≤ L) :
    ((Finset.range L).filter (fun j => j + 1 ≤ a)).card = a := by
  have : (Finset.range L).filter (fun j => j + 1 ≤ a) = Finset.range a := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this, Finset.card_range]

lemma level_decomp (c : ℝ) (s : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℕ) (L : ℕ)
    (ha : ∀ k ∈ s, a k ≤ L) :
    cubeSum c s (fun k => (a k : ℂ) * (1 / (L : ℂ))) =
      (1 / (L : ℂ)) • ∑ j ∈ Finset.range L,
        cubeSum c (s.filter (fun k => j + 1 ≤ a k)) (fun _ => 1) := by
  funext ω
  simp only [cubeSum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, one_mul]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← Finset.sum_filter, Finset.sum_const, range_filter_card L (a k) (ha k hk), nsmul_eq_mul]
  ring

section Main

variable {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {q q₀ A : ℝ} (hq : 1 ≤ q) (hqq : q < q₀) (hA : 0 ≤ A)
  (h4 : ∀ t : Finset (Fin n → ℤ), eLpNorm (cubeSum c t (fun _ => 1)) (ENNReal.ofReal q)
      (sphereMeasure n) ≤ ENNReal.ofReal (A * ((t.card : ℝ) * c ^ n) ^ (1 / q₀)))
include hc hq hqq hA h4

/-- The constant of the bound for nonnegative coefficients. -/
noncomputable def K2 (n : ℕ) (q q₀ A : ℝ) : ℝ≥0∞ :=
  2 * (sphereMeasure n Set.univ ^ (ENNReal.ofReal q).toReal⁻¹) + ENNReal.ofReal (A / (1 - q / q₀))

lemma level_bound (s : Finset (Fin n → ℤ)) (b : (Fin n → ℤ) → ℝ) (hb : ∀ k, 0 ≤ b k)
    (hT : ∑ k ∈ s, b k ^ q * c ^ n ≤ 1) (a : (Fin n → ℤ) → ℕ) (L : ℕ) (hL : 1 ≤ L)
    (haL : ∀ k ∈ s, a k ≤ L) (hab : ∀ k ∈ s, (a k : ℝ) ≤ L * b k) :
    eLpNorm (cubeSum c s (fun k => (a k : ℂ) * (1 / (L : ℂ)))) (ENNReal.ofReal q)
      (sphereMeasure n) ≤ ENNReal.ofReal (A / (1 - q / q₀)) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hq0 : 0 < q₀ := by linarith
  set a' := q / q₀ with ha'
  have ha0 : 0 ≤ a' := div_nonneg (by linarith) hq0.le
  have ha1 : a' < 1 := (div_lt_one hq0).mpr hqq
  rw [level_decomp c s a L haL, eLpNorm_const_smul]
  -- each level
  have hlev : ∀ j ∈ Finset.range L,
      eLpNorm (cubeSum c (s.filter (fun k => j + 1 ≤ a k)) (fun _ => 1)) (ENNReal.ofReal q)
        (sphereMeasure n) ≤ ENNReal.ofReal (A * (((j : ℝ) + 1) / L) ^ (-a')) := by
    intro j _
    refine (h4 _).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ hA
    set t := s.filter (fun k => j + 1 ≤ a k)
    have hx : 0 < ((j : ℝ) + 1) / L := div_pos (by positivity) hL'
    have hcheb : (t.card : ℝ) * c ^ n ≤ ((((j : ℝ) + 1) / L) ^ q)⁻¹ := by
      have hxq : 0 < (((j : ℝ) + 1) / L) ^ q := Real.rpow_pos_of_pos hx q
      rw [← one_div, le_div_iff₀ hxq]
      have : ∀ k ∈ t, (((j : ℝ) + 1) / L) ^ q * c ^ n ≤ b k ^ q * c ^ n := by
        intro k hk
        rw [Finset.mem_filter] at hk
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply Real.rpow_le_rpow hx.le _ (by linarith)
        rw [div_le_iff₀ hL']
        have h1 : ((j : ℝ) + 1) ≤ a k := by exact_mod_cast hk.2
        linarith [hab k hk.1]
      have hsum := Finset.sum_le_sum this
      rw [Finset.sum_const, nsmul_eq_mul] at hsum
      have hsub : ∑ k ∈ t, b k ^ q * c ^ n ≤ ∑ k ∈ s, b k ^ q * c ^ n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun k _ _ => by have := hb k; positivity)
      nlinarith
    calc ((t.card : ℝ) * c ^ n) ^ (1 / q₀) ≤ (((((j : ℝ) + 1) / L) ^ q)⁻¹) ^ (1 / q₀) :=
          Real.rpow_le_rpow (by positivity) hcheb (by positivity)
      _ = (((j : ℝ) + 1) / L) ^ (-a') := by
          rw [← Real.rpow_neg hx.le, ← Real.rpow_mul hx.le]
          congr 1; rw [ha']; ring
  calc ‖(1 / (L : ℂ))‖ₑ * eLpNorm (∑ j ∈ Finset.range L,
          cubeSum c (s.filter (fun k => j + 1 ≤ a k)) (fun _ => 1)) (ENNReal.ofReal q)
          (sphereMeasure n)
        ≤ ‖(1 / (L : ℂ))‖ₑ * ∑ j ∈ Finset.range L,
          ENNReal.ofReal (A * (((j : ℝ) + 1) / L) ^ (-a')) := by
          gcongr
          refine (eLpNorm_sum_le (fun j _ => aesm_cubeSum _ _ _)
            (by rw [ENNReal.one_le_ofReal]; exact hq)).trans ?_
          exact Finset.sum_le_sum hlev
    _ = ENNReal.ofReal (A * ((1 / (L : ℝ)) *
          ∑ j ∈ Finset.range L, (((j : ℝ) + 1) / L) ^ (-a'))) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
          have : ‖(1 / (L : ℂ))‖ₑ = ENNReal.ofReal (1 / (L : ℝ)) := by
            rw [← ofReal_norm_eq_enorm]; congr 1
            rw [norm_div, norm_one, Complex.norm_natCast]
          rw [this, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ENNReal.ofReal (A / (1 - q / q₀)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [div_eq_mul_one_div A]
          exact mul_le_mul_of_nonneg_left (riemann_sum_le ha0 ha1 L hL) hA

end Main

end TaoBR.CU

end
end

section
section
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace

namespace TaoBR.CU

variable {n : ℕ}

section Main

variable {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {q q₀ A : ℝ} (hq : 1 ≤ q) (hqq : q < q₀) (hA : 0 ≤ A)
  (h4 : ∀ t : Finset (Fin n → ℤ), eLpNorm (cubeSum c t (fun _ => 1)) (ENNReal.ofReal q)
      (sphereMeasure n) ≤ ENNReal.ofReal (A * ((t.card : ℝ) * c ^ n) ^ (1 / q₀)))
include hc hq hqq hA h4

lemma cube_bound_nonneg (s : Finset (Fin n → ℤ)) (b : (Fin n → ℤ) → ℝ) (hb : ∀ k, 0 ≤ b k)
    (hT : ∑ k ∈ s, b k ^ q * c ^ n ≤ 1) :
    eLpNorm (cubeSum c s (fun k => (b k : ℂ))) (ENNReal.ofReal q) (sphereMeasure n) ≤
      K2 n q q₀ A := by
  set L : ℕ := ⌈(s.card : ℝ) * c ^ n⌉₊ + 1 with hLdef
  have hL : 1 ≤ L := by omega
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hLbig : (s.card : ℝ) * c ^ n ≤ L := by
    rw [hLdef]; push_cast; linarith [Nat.le_ceil ((s.card : ℝ) * c ^ n)]
  set u : (Fin n → ℤ) → ℝ := fun k => min (b k) 1
  set a : (Fin n → ℤ) → ℕ := fun k => ⌊(L : ℝ) * u k⌋₊
  have hu0 : ∀ k, 0 ≤ u k := fun k => le_min (hb k) zero_le_one
  have hu1 : ∀ k, u k ≤ 1 := fun k => min_le_right _ _
  have haL : ∀ k ∈ s, a k ≤ L := by
    intro k _
    have : (L : ℝ) * u k ≤ L := by nlinarith [hu1 k]
    exact Nat.floor_le_of_le (by exact_mod_cast this) |> fun h => by exact_mod_cast h
  have hab : ∀ k ∈ s, (a k : ℝ) ≤ L * b k := by
    intro k _
    have := Nat.floor_le (show 0 ≤ (L : ℝ) * u k by have := hu0 k; positivity)
    have hub : u k ≤ b k := min_le_left _ _
    calc (a k : ℝ) ≤ L * u k := this
      _ ≤ L * b k := by gcongr
  -- the three pieces
  set r : (Fin n → ℤ) → ℝ := fun k => u k - a k * (1 / L)
  set v : (Fin n → ℤ) → ℝ := fun k => b k - u k
  have hdec : (fun k => (b k : ℂ)) =
      fun k => ((a k : ℂ) * (1 / (L : ℂ)) + (r k : ℂ)) + (v k : ℂ) := by
    funext k; simp only [r, v]; push_cast; ring
  have hr : ∀ k, 0 ≤ r k ∧ r k ≤ 1 / L := by
    intro k
    have h1 := Nat.floor_le (show 0 ≤ (L : ℝ) * u k by have := hu0 k; positivity)
    have h2 := Nat.lt_floor_add_one ((L : ℝ) * u k)
    simp only [r]
    constructor
    · rw [sub_nonneg, mul_one_div, div_le_iff₀ hL']; linarith
    · have e : u k - (a k : ℝ) * (1 / L) = ((L : ℝ) * u k - a k) / L := by field_simp
      rw [e, div_le_div_iff_of_pos_right hL']; linarith
  have hv : ∀ k, 0 ≤ v k ∧ v k ≤ b k ^ q := by
    intro k
    simp only [v, u]
    constructor
    · linarith [min_le_left (b k) 1]
    · rcases le_total (b k) 1 with h | h
      · rw [min_eq_left h, sub_self]; exact Real.rpow_nonneg (hb k) _
      · rw [min_eq_right h]
        calc b k - 1 ≤ b k := by linarith
          _ = b k ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ b k ^ q := Real.rpow_le_rpow_of_exponent_le h hq
  rw [hdec, cubeSum_add, cubeSum_add]
  have hbound1 : eLpNorm (cubeSum c s (fun k => (r k : ℂ))) (ENNReal.ofReal q) (sphereMeasure n) ≤
      sphereMeasure n Set.univ ^ (ENNReal.ofReal q).toReal⁻¹ * ENNReal.ofReal 1 := by
    apply eLpNorm_le_of_bound
    intro ω
    refine (norm_cubeSum_le hc.le s _ ω).trans ?_
    calc ∑ k ∈ s, ‖(r k : ℂ)‖ * c ^ n ≤ ∑ k ∈ s, (1 / (L : ℝ)) * c ^ n := by
          gcongr with k hk
          rw [Complex.norm_real, Real.norm_of_nonneg (hr k).1]; exact (hr k).2
      _ = (s.card : ℝ) * c ^ n / L := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 1 := by rw [div_le_one hL']; exact hLbig
  have hbound2 : eLpNorm (cubeSum c s (fun k => (v k : ℂ))) (ENNReal.ofReal q) (sphereMeasure n) ≤
      sphereMeasure n Set.univ ^ (ENNReal.ofReal q).toReal⁻¹ * ENNReal.ofReal 1 := by
    apply eLpNorm_le_of_bound
    intro ω
    refine (norm_cubeSum_le hc.le s _ ω).trans ?_
    calc ∑ k ∈ s, ‖(v k : ℂ)‖ * c ^ n ≤ ∑ k ∈ s, b k ^ q * c ^ n := by
          gcongr with k hk
          rw [Complex.norm_real, Real.norm_of_nonneg (hv k).1]; exact (hv k).2
      _ ≤ 1 := hT
  have hbound3 := level_bound hc hq hqq hA h4 s b hb hT a L hL haL hab
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by rw [ENNReal.one_le_ofReal]; exact hq
  calc eLpNorm (cubeSum c s (fun k => (a k : ℂ) * (1 / (L : ℂ))) + cubeSum c s (fun k => (r k : ℂ))
        + cubeSum c s (fun k => (v k : ℂ))) (ENNReal.ofReal q) (sphereMeasure n)
      ≤ eLpNorm (cubeSum c s (fun k => (a k : ℂ) * (1 / (L : ℂ)))) (ENNReal.ofReal q)
          (sphereMeasure n) + eLpNorm (cubeSum c s (fun k => (r k : ℂ))) (ENNReal.ofReal q)
          (sphereMeasure n) + eLpNorm (cubeSum c s (fun k => (v k : ℂ))) (ENNReal.ofReal q)
          (sphereMeasure n) := by
        refine (eLpNorm_add_le ((aesm_cubeSum _ _ _).add (aesm_cubeSum _ _ _))
          (aesm_cubeSum _ _ _) hq1).trans ?_
        gcongr
        exact eLpNorm_add_le (aesm_cubeSum _ _ _) (aesm_cubeSum _ _ _) hq1
    _ ≤ ENNReal.ofReal (A / (1 - q / q₀)) +
          sphereMeasure n Set.univ ^ (ENNReal.ofReal q).toReal⁻¹ * ENNReal.ofReal 1 +
          sphereMeasure n Set.univ ^ (ENNReal.ofReal q).toReal⁻¹ * ENNReal.ofReal 1 := by
        gcongr
    _ = K2 n q q₀ A := by
        rw [K2, ENNReal.ofReal_one, mul_one]; ring

/-- The bound for complex coefficients: `‖Σ a_k φ_k‖_{L^q(σ)} ≤ 4 K₂ (Σ |a_k|^q c^n)^{1/q}`. -/
lemma cube_bound (s : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℂ) :
    eLpNorm (cubeSum c s a) (ENNReal.ofReal q) (sphereMeasure n) ≤
      4 * K2 n q q₀ A * ENNReal.ofReal ((∑ k ∈ s, ‖a k‖ ^ q * c ^ n) ^ (1 / q)) := by
  set T := ∑ k ∈ s, ‖a k‖ ^ q * c ^ n with hTdef
  have hq0 : 0 < q := by linarith
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun k _ => by positivity
  rcases hT0.eq_or_lt with hT | hT
  · -- all coefficients vanish
    have hz : ∀ k ∈ s, a k = 0 := by
      intro k hk
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).mp hT.symm k hk
      rcases mul_eq_zero.mp h with h | h
      · exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg _) hq0.ne').mp h)
      · exact absurd h (pow_ne_zero _ hc.ne')
    have : cubeSum c s a = 0 := by
      funext ω; simp only [cubeSum, Pi.zero_apply]
      exact Finset.sum_eq_zero fun k hk => by rw [hz k hk, zero_mul]
    rw [this, eLpNorm_zero]; exact bot_le
  · set lam := T ^ (1 / q) with hlam
    have hlam0 : 0 < lam := Real.rpow_pos_of_pos hT _
    have hlamq : lam ^ q = T := by
      rw [hlam, ← Real.rpow_mul hT.le, one_div_mul_cancel hq0.ne', Real.rpow_one]
    set b1 : (Fin n → ℤ) → ℝ := fun k => max (a k).re 0 / lam
    set b2 : (Fin n → ℤ) → ℝ := fun k => max (-(a k).re) 0 / lam
    set b3 : (Fin n → ℤ) → ℝ := fun k => max (a k).im 0 / lam
    set b4 : (Fin n → ℤ) → ℝ := fun k => max (-(a k).im) 0 / lam
    have hpos : ∀ (x : ℝ), 0 ≤ max x 0 / lam := fun x => div_nonneg (le_max_right _ _) hlam0.le
    have hsmall : ∀ (x : ℝ) (k : Fin n → ℤ), |x| ≤ ‖a k‖ →
        (max x 0 / lam) ^ q * c ^ n ≤ ‖a k‖ ^ q * c ^ n / T := by
      intro x k hx
      rw [div_eq_mul_inv (‖a k‖ ^ q * c ^ n), mul_right_comm]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [Real.div_rpow (le_max_right _ _) hlam0.le, hlamq, div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply Real.rpow_le_rpow (le_max_right _ _) _ hq0.le
      exact max_le (le_trans (le_abs_self x) hx) (norm_nonneg _)
    have hT1 : ∀ (x : (Fin n → ℤ) → ℝ), (∀ k, |x k| ≤ ‖a k‖) →
        ∑ k ∈ s, (max (x k) 0 / lam) ^ q * c ^ n ≤ 1 := by
      intro x hx
      calc ∑ k ∈ s, (max (x k) 0 / lam) ^ q * c ^ n ≤ ∑ k ∈ s, ‖a k‖ ^ q * c ^ n / T :=
            Finset.sum_le_sum fun k _ => hsmall (x k) k (hx k)
        _ = 1 := by rw [← Finset.sum_div, ← hTdef, div_self hT.ne']
    have hre : ∀ k, |(a k).re| ≤ ‖a k‖ := fun k => Complex.abs_re_le_norm _
    have him : ∀ k, |(a k).im| ≤ ‖a k‖ := fun k => Complex.abs_im_le_norm _
    have B1 := cube_bound_nonneg hc hq hqq hA h4 s b1 (fun k => hpos _) (hT1 _ hre)
    have B2 := cube_bound_nonneg hc hq hqq hA h4 s b2 (fun k => hpos _)
      (hT1 (fun k => -(a k).re) (fun k => by rw [abs_neg]; exact hre k))
    have B3 := cube_bound_nonneg hc hq hqq hA h4 s b3 (fun k => hpos _) (hT1 _ him)
    have B4 := cube_bound_nonneg hc hq hqq hA h4 s b4 (fun k => hpos _)
      (hT1 (fun k => -(a k).im) (fun k => by rw [abs_neg]; exact him k))
    have hdec : cubeSum c s a = (lam : ℂ) • (cubeSum c s (fun k => (b1 k : ℂ)) +
        (-1 : ℂ) • cubeSum c s (fun k => (b2 k : ℂ)) + Complex.I • cubeSum c s (fun k => (b3 k : ℂ))
        + (-Complex.I) • cubeSum c s (fun k => (b4 k : ℂ))) := by
      funext ω
      simp only [cubeSum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk : a k = (lam : ℂ) * ((b1 k : ℂ) - b2 k + Complex.I * (b3 k - b4 k)) := by
        simp only [b1, b2, b3, b4]
        have e1 : max (a k).re 0 / lam - max (-(a k).re) 0 / lam = (a k).re / lam := by
          rw [← sub_div]; congr 1
          rcases le_total 0 (a k).re with h | h
          · rw [max_eq_left h, max_eq_right (by linarith)]; ring
          · rw [max_eq_right h, max_eq_left (by linarith)]; ring
        have e2 : max (a k).im 0 / lam - max (-(a k).im) 0 / lam = (a k).im / lam := by
          rw [← sub_div]; congr 1
          rcases le_total 0 (a k).im with h | h
          · rw [max_eq_left h, max_eq_right (by linarith)]; ring
          · rw [max_eq_right h, max_eq_left (by linarith)]; ring
        have : ((max (a k).re 0 / lam : ℝ) : ℂ) - ((max (-(a k).re) 0 / lam : ℝ) : ℂ) +
            Complex.I * (((max (a k).im 0 / lam : ℝ) : ℂ) - ((max (-(a k).im) 0 / lam : ℝ) : ℂ))
            = (((a k).re / lam : ℝ) : ℂ) + Complex.I * (((a k).im / lam : ℝ) : ℂ) := by
          rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, e1, e2]
        rw [this]
        apply Complex.ext <;> simp [hlam0.ne'] <;> field_simp
      rw [hk]; ring
    have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by rw [ENNReal.one_le_ofReal]; exact hq
    clear_value b1 b2 b3 b4
    rw [hdec, eLpNorm_const_smul]
    have hm : ∀ (z : ℂ), ‖z‖ₑ = 1 → ∀ (F : sphere (0 : E n) 1 → ℂ),
        eLpNorm (z • F) (ENNReal.ofReal q) (sphereMeasure n) =
          eLpNorm F (ENNReal.ofReal q) (sphereMeasure n) := by
      intro z hz F; rw [eLpNorm_const_smul, hz, one_mul]
    have hlamE : ‖(lam : ℂ)‖ₑ = ENNReal.ofReal lam := by
      rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg hlam0.le]
    rw [hlamE, mul_comm (4 * K2 n q q₀ A)]
    gcongr
    have a1 := aesm_cubeSum c s (fun k => (b1 k : ℂ))
    have a2 := (aesm_cubeSum c s (fun k => (b2 k : ℂ))).const_smul (-1 : ℂ)
    have a3 := (aesm_cubeSum c s (fun k => (b3 k : ℂ))).const_smul Complex.I
    have a4 := (aesm_cubeSum c s (fun k => (b4 k : ℂ))).const_smul (-Complex.I)
    have hI : ‖Complex.I‖ₑ = 1 := by
      rw [← ofReal_norm_eq_enorm, Complex.norm_I, ENNReal.ofReal_one]
    have hnI : ‖-Complex.I‖ₑ = 1 := by rw [enorm_neg, hI]
    have hn1 : ‖(-1 : ℂ)‖ₑ = 1 := by rw [enorm_neg, enorm_one]
    calc _ ≤ eLpNorm (cubeSum c s (fun k => (b1 k : ℂ))) (ENNReal.ofReal q) (sphereMeasure n) +
          eLpNorm ((-1 : ℂ) • cubeSum c s (fun k => (b2 k : ℂ))) (ENNReal.ofReal q)
            (sphereMeasure n) +
          eLpNorm (Complex.I • cubeSum c s (fun k => (b3 k : ℂ))) (ENNReal.ofReal q)
            (sphereMeasure n) +
          eLpNorm ((-Complex.I) • cubeSum c s (fun k => (b4 k : ℂ))) (ENNReal.ofReal q)
            (sphereMeasure n) := by
          refine (eLpNorm_add_le ((a1.add a2).add a3) a4 hq1).trans ?_
          gcongr ?_ + _
          refine (eLpNorm_add_le (a1.add a2) a3 hq1).trans ?_
          gcongr ?_ + _
          exact eLpNorm_add_le a1 a2 hq1
      _ = eLpNorm (cubeSum c s (fun k => (b1 k : ℂ))) (ENNReal.ofReal q) (sphereMeasure n) +
          eLpNorm (cubeSum c s (fun k => (b2 k : ℂ))) (ENNReal.ofReal q) (sphereMeasure n) +
          eLpNorm (cubeSum c s (fun k => (b3 k : ℂ))) (ENNReal.ofReal q) (sphereMeasure n) +
          eLpNorm (cubeSum c s (fun k => (b4 k : ℂ))) (ENNReal.ofReal q) (sphereMeasure n) := by
          rw [hm _ hn1, hm _ hI, hm _ hnI]
      _ ≤ K2 n q q₀ A + K2 n q q₀ A + K2 n q q₀ A + K2 n q q₀ A := by gcongr
      _ = 4 * K2 n q q₀ A := by ring

end Main

end TaoBR.CU

end
end

section
section
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace

namespace TaoBR.CU

variable {n : ℕ}

/-- The unit box `[0, 1)ⁿ`. -/
def U (n : ℕ) : Set (E n) := {z | ∀ i, z i ∈ Set.Ico (0 : ℝ) 1}

lemma U_eq : U n = (WithLp.ofLp : E n → (Fin n → ℝ)) ⁻¹'
    Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1) := by
  ext z; simp [U]

lemma measurableSet_U : MeasurableSet (U n) := by
  rw [U_eq]
  exact (MeasurableSet.univ_pi fun _ => measurableSet_Ico).preimage (WithLp.measurable_ofLp 2 _)

lemma volume_U : volume (U n) = 1 := by
  rw [U_eq, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    ((MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet), volume_pi,
    Measure.pi_pi]
  simp

/-- The lattice points in a box around `0`, enough to tile `closedBall 0 R`. -/
noncomputable def box (n : ℕ) (R : ℝ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(⌈R⌉ + 1)) (⌈R⌉ + 1)

/-- The coordinatewise floor. -/
noncomputable def floorVec (x : E n) : Fin n → ℤ := fun i => ⌊x i⌋

lemma sub_latt_mem_U_iff (x : E n) (k : Fin n → ℤ) : x - latt k ∈ U n ↔ k = floorVec x := by
  simp only [U, Set.mem_setOf_eq, PiLp.sub_apply, latt_apply, Set.mem_Ico, sub_nonneg,
    floorVec]
  constructor
  · intro h; funext i
    show k i = ⌊x i⌋
    rw [eq_comm, Int.floor_eq_iff]; constructor <;> linarith [(h i).1, (h i).2]
  · intro h i
    rw [h]
    show (⌊x i⌋ : ℝ) ≤ x i ∧ x i - ⌊x i⌋ < 1
    exact ⟨Int.floor_le _, by linarith [Int.lt_floor_add_one (x i)]⟩

lemma floorVec_mem_box {R : ℝ} {x : E n} (hx : ‖x‖ ≤ R) : floorVec x ∈ box n R := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc, floorVec]
  intro i
  have h1 : |x i| ≤ R := by
    have := PiLp.norm_apply_le x i
    rw [Real.norm_eq_abs] at this; linarith
  have h2 := abs_le.mp h1
  have hc := Int.le_ceil R
  constructor
  · have : (-(⌈R⌉ + 1) : ℤ) < ⌊x i⌋ + 1 := by
      rw [← Int.cast_lt (R := ℝ)]; push_cast; linarith [Int.lt_floor_add_one (x i)]
    omega
  · have : (⌊x i⌋ : ℝ) ≤ ⌈R⌉ := by linarith [Int.floor_le (x i)]
    have : ⌊x i⌋ ≤ ⌈R⌉ := by exact_mod_cast this
    omega

/-- A function supported in `closedBall 0 R` is the sum of its pieces on the translated boxes. -/
lemma sum_indicator_tile {M : Type*} [AddCommMonoid M] {R : ℝ} (F : E n → M)
    (hF : ∀ x, F x ≠ 0 → ‖x‖ ≤ R) (x : E n) :
    ∑ k ∈ box n R, {y | y - latt k ∈ U n}.indicator F x = F x := by
  by_cases hx : F x = 0
  · rw [hx]; exact Finset.sum_eq_zero fun k _ => by
      by_cases h : x ∈ {y | y - latt k ∈ U n}
      · rw [Set.indicator_of_mem h, hx]
      · rw [Set.indicator_of_notMem h]
  · rw [Finset.sum_eq_single (floorVec x)]
    · rw [Set.indicator_of_mem]; exact (sub_latt_mem_U_iff x _).mpr rfl
    · intro k _ hk
      rw [Set.indicator_of_notMem]
      exact fun h => hk ((sub_latt_mem_U_iff x k).mp h)
    · intro h; exact absurd (floorVec_mem_box (hF x hx)) h

lemma tile_piece_indicator {M : Type*} [Zero M] (F : E n → M) (k : Fin n → ℤ) (z : E n) :
    {y | y - latt k ∈ U n}.indicator F (z + latt k) = (U n).indicator (fun z => F (z + latt k)) z := by
  by_cases h : z ∈ U n
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem]; simpa using h
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem]; simpa using h

lemma measurableSet_tile (k : Fin n → ℤ) : MeasurableSet {y : E n | y - latt k ∈ U n} :=
  measurableSet_U.preimage (measurable_id.sub_const _)

lemma indicator_sum_comm {M : Type*} [AddCommMonoid M] (s : Finset (Fin n → ℤ))
    (G : (Fin n → ℤ) → E n → M) (z : E n) :
    ∑ k ∈ s, (U n).indicator (G k) z = (U n).indicator (fun z => ∑ k ∈ s, G k z) z := by
  by_cases h : z ∈ U n
  · simp only [Set.indicator_of_mem h]
  · simp only [Set.indicator_of_notMem h, Finset.sum_const_zero]

/-- Tiling for integrals. -/
lemma integral_tile {R : ℝ} (F : E n → ℂ) (hFi : Integrable F)
    (hF : ∀ x, F x ≠ 0 → ‖x‖ ≤ R) :
    ∫ x, F x = ∫ z, (U n).indicator (fun z => ∑ k ∈ box n R, F (z + latt k)) z := by
  calc ∫ x, F x = ∫ x, ∑ k ∈ box n R, {y | y - latt k ∈ U n}.indicator F x := by
        congr 1; funext x; rw [sum_indicator_tile F hF x]
    _ = ∑ k ∈ box n R, ∫ x, {y | y - latt k ∈ U n}.indicator F x := by
        rw [integral_finset_sum]
        exact fun k _ => hFi.indicator (measurableSet_tile k)
    _ = ∑ k ∈ box n R, ∫ z, (U n).indicator (fun z => F (z + latt k)) z := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← integral_add_right_eq_self (μ := (volume : Measure (E n))) _ (latt k)]
        congr 1; funext z; exact tile_piece_indicator F k z
    _ = ∫ z, ∑ k ∈ box n R, (U n).indicator (fun z => F (z + latt k)) z := by
        rw [integral_finset_sum]
        exact fun k _ => (hFi.comp_add_right (latt k)).indicator measurableSet_U
    _ = _ := by
        congr 1; funext z
        exact indicator_sum_comm _ _ _

/-- Tiling for lower integrals. -/
lemma lintegral_tile {R : ℝ} (F : E n → ℝ≥0∞) (hFm : Measurable F)
    (hF : ∀ x, F x ≠ 0 → ‖x‖ ≤ R) :
    ∫⁻ x, F x = ∫⁻ z in U n, ∑ k ∈ box n R, F (z + latt k) := by
  calc ∫⁻ x, F x = ∫⁻ x, ∑ k ∈ box n R, {y | y - latt k ∈ U n}.indicator F x := by
        congr 1; funext x; rw [sum_indicator_tile F hF x]
    _ = ∑ k ∈ box n R, ∫⁻ x, {y | y - latt k ∈ U n}.indicator F x := by
        rw [lintegral_finset_sum]
        exact fun k _ => hFm.indicator (measurableSet_tile k)
    _ = ∑ k ∈ box n R, ∫⁻ z, (U n).indicator (fun z => F (z + latt k)) z := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← lintegral_add_right_eq_self (μ := (volume : Measure (E n))) _ (latt k)]
        congr 1; funext z; exact tile_piece_indicator F k z
    _ = ∫⁻ z, ∑ k ∈ box n R, (U n).indicator (fun z => F (z + latt k)) z := by
        rw [lintegral_finset_sum]
        exact fun k _ => (hFm.comp (measurable_id.add_const _)).indicator measurableSet_U
    _ = _ := by
        rw [← lintegral_indicator measurableSet_U]
        congr 1; funext z
        exact indicator_sum_comm _ _ _

end TaoBR.CU

end
end

section
section
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace

namespace TaoBR.CU

variable {n : ℕ}

/-- The cube function with coefficients `f(z + k)`, restricted to the sphere. -/
noncomputable def Phi (c R : ℝ) (f : E n → ℂ) (z : E n) (ω : sphere (0 : E n) 1) : ℂ :=
  cubeSum c (box n R) (fun k => f (z + latt k)) ω

lemma continuous_Phi (c R : ℝ) {f : E n → ℂ} (hf : Continuous f) :
    Continuous (fun p : E n × sphere (0 : E n) 1 => Phi c R f p.1 p.2) := by
  unfold Phi cubeSum
  refine continuous_finset_sum _ fun k _ => ?_
  exact (hf.comp (continuous_fst.add continuous_const)).mul
    ((continuous_phi c k).comp (continuous_subtype_val.comp continuous_snd))

lemma restriction_pointwise {c : ℝ} {m : ℝ} (hm0 : 0 < m)
    (hm : ∀ ω : E n, ‖ω‖ = 1 → m ≤ ‖phi c 0 ω‖) {R : ℝ} (f : E n → ℂ) (hfi : Integrable f)
    (hF : ∀ x, f x ≠ 0 → ‖x‖ ≤ R) (ω : sphere (0 : E n) 1) :
    ‖restriction f ω‖ₑ ≤ ENNReal.ofReal m⁻¹ * ∫⁻ z in U n, ‖Phi c R f z ω‖ₑ := by
  set F : E n → ℂ := fun x => 𝐞 (-⟪x, (ω : E n)⟫) • f x
  have hFi : Integrable F := (Real.fourierIntegral_convergent_iff (ω : E n)).2 hfi
  have hFs : ∀ x, F x ≠ 0 → ‖x‖ ≤ R := by
    intro x hx; apply hF x; intro h; apply hx; simp [F, h]
  have h1 : restriction f ω = ∫ z, (U n).indicator (fun z => ∑ k ∈ box n R, F (z + latt k)) z := by
    rw [← integral_tile F hFi hFs]; rfl
  rw [h1]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  simp_rw [enorm_indicator_eq_indicator_enorm]
  rw [lintegral_indicator measurableSet_U, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun z => ?_
  have hω : ‖(ω : E n)‖ = 1 := by simpa using ω.2
  have hph := hm _ hω
  set S : ℂ := ∑ k ∈ box n R, (𝐞 (-⟪latt k, (ω : E n)⟫) : ℂ) * f (z + latt k)
  have hsum : ∑ k ∈ box n R, F (z + latt k) = (𝐞 (-⟪z, (ω : E n)⟫) : ℂ) * S := by
    simp only [F, S, Finset.mul_sum, Circle.smul_def, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_add_left, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
  have hPhi : Phi c R f z ω = phi c 0 (ω : E n) * S := by
    simp only [Phi, cubeSum, S, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [phi_translate, Circle.smul_def, smul_eq_mul]; ring
  rw [hsum, hPhi, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul
    (inv_nonneg.mpr hm0.le)]
  apply ENNReal.ofReal_le_ofReal
  rw [norm_mul, norm_mul, Circle.norm_coe, one_mul]
  rw [← mul_assoc, ← div_eq_inv_mul]
  have h1 : 1 ≤ ‖phi c 0 (ω : E n)‖ / m := by rw [le_div_iff₀ hm0]; linarith
  nlinarith [norm_nonneg S]

/-- Jensen on the unit box: `(∫_U |G|)^q ≤ ∫_U |G|^q`. -/
lemma jensen_U {q : ℝ} (hq : 1 ≤ q) (G : E n → ℂ) (hG : AEStronglyMeasurable G
    (volume.restrict (U n))) :
    (∫⁻ z in U n, ‖G z‖ₑ) ^ q ≤ ∫⁻ z in U n, ‖G z‖ₑ ^ q := by
  have hq0 : 0 < q := by linarith
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := ENNReal.ofReal q)
    (by rw [ENNReal.one_le_ofReal]; exact hq) hG
  rw [Measure.restrict_apply_univ, volume_U, ENNReal.one_rpow, mul_one,
    eLpNorm_one_eq_lintegral_enorm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq0.le] at h
  calc (∫⁻ z in U n, ‖G z‖ₑ) ^ q ≤ ((∫⁻ z in U n, ‖G z‖ₑ ^ q) ^ (1 / q)) ^ q :=
        ENNReal.rpow_le_rpow h hq0.le
    _ = _ := by rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]

end TaoBR.CU

end
end

section
section
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace

namespace TaoBR.CU

variable {n : ℕ}

instance : IsFiniteMeasure (sphereMeasure n) := by unfold sphereMeasure; infer_instance

section Main

variable {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {q q₀ A : ℝ} (hq : 1 ≤ q) (hqq : q < q₀) (hA : 0 ≤ A)
  (h4 : ∀ t : Finset (Fin n → ℤ), eLpNorm (cubeSum c t (fun _ => 1)) (ENNReal.ofReal q)
      (sphereMeasure n) ≤ ENNReal.ofReal (A * ((t.card : ℝ) * c ^ n) ^ (1 / q₀)))
include hc hq hqq hA h4

lemma Phi_lintegral_le (R : ℝ) (f : E n → ℂ) (z : E n) :
    ∫⁻ ω, ‖Phi c R f z ω‖ₑ ^ q ∂(sphereMeasure n) ≤
      (4 * K2 n q q₀ A) ^ q * (ENNReal.ofReal (c ^ n) *
        ∑ k ∈ box n R, ‖f (z + latt k)‖ₑ ^ q) := by
  have hq0 : 0 < q := by linarith
  have hb := cube_bound hc hq hqq hA h4 (box n R) (fun k => f (z + latt k))
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq0.le] at hb
  have hb' := ENNReal.rpow_le_rpow hb hq0.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le, ← Real.rpow_mul (by positivity),
    one_div_mul_cancel hq0.ne', Real.rpow_one] at hb'
  refine hb'.trans (le_of_eq ?_)
  congr 1
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ENNReal.ofReal_mul (by positivity), mul_comm,
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0.le, ofReal_norm_eq_enorm]

lemma restriction_eLpNorm_le {m : ℝ} (hm0 : 0 < m)
    (hm : ∀ ω : E n, ‖ω‖ = 1 → m ≤ ‖phi c 0 ω‖) {R : ℝ} (f : E n → ℂ) (hf : Continuous f)
    (hfi : Integrable f) (hF : ∀ x, f x ≠ 0 → ‖x‖ ≤ R) :
    eLpNorm (restriction f) (ENNReal.ofReal q) (sphereMeasure n) ≤
      ENNReal.ofReal m⁻¹ * (4 * K2 n q q₀ A) * ENNReal.ofReal (c ^ n) ^ (1 / q) *
        eLpNorm f (ENNReal.ofReal q) volume := by
  have hq0 : 0 < q := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith) ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq0.le]
  have hmeas : Measurable (fun p : E n × sphere (0 : E n) 1 => ‖Phi c R f p.1 p.2‖ₑ ^ q) :=
    ((continuous_Phi c R hf).measurable.enorm).pow_const _
  have key : ∫⁻ ω, ‖restriction f ω‖ₑ ^ q ∂(sphereMeasure n) ≤
      (ENNReal.ofReal m⁻¹ * (4 * K2 n q q₀ A)) ^ q * (ENNReal.ofReal (c ^ n) * ∫⁻ x, ‖f x‖ₑ ^ q) := by
    calc ∫⁻ ω, ‖restriction f ω‖ₑ ^ q ∂(sphereMeasure n)
        ≤ ∫⁻ ω, ENNReal.ofReal m⁻¹ ^ q * ((∫⁻ z in U n, ‖Phi c R f z ω‖ₑ) ^ q)
            ∂(sphereMeasure n) := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
          exact ENNReal.rpow_le_rpow (restriction_pointwise hm0 hm f hfi hF ω) hq0.le
      _ ≤ ∫⁻ ω, ENNReal.ofReal m⁻¹ ^ q * (∫⁻ z in U n, ‖Phi c R f z ω‖ₑ ^ q)
            ∂(sphereMeasure n) := by
          refine lintegral_mono fun ω => ?_
          gcongr
          exact jensen_U hq _ ((continuous_Phi c R hf).comp
            (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      _ = ENNReal.ofReal m⁻¹ ^ q * ∫⁻ z in U n, (∫⁻ ω, ‖Phi c R f z ω‖ₑ ^ q
            ∂(sphereMeasure n)) := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top),
            lintegral_lintegral_swap]
          exact (hmeas.comp measurable_swap).aemeasurable
      _ ≤ ENNReal.ofReal m⁻¹ ^ q * ∫⁻ z in U n, (4 * K2 n q q₀ A) ^ q *
            (ENNReal.ofReal (c ^ n) * ∑ k ∈ box n R, ‖f (z + latt k)‖ₑ ^ q) := by
          gcongr with z
          exact Phi_lintegral_le hc hq hqq hA h4 R f z
      _ = ENNReal.ofReal m⁻¹ ^ q * ((4 * K2 n q q₀ A) ^ q * (ENNReal.ofReal (c ^ n) *
            ∫⁻ z in U n, ∑ k ∈ box n R, ‖f (z + latt k)‖ₑ ^ q)) := by
          rw [lintegral_const_mul' _ _ ?_, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine ENNReal.rpow_ne_top_of_nonneg hq0.le ?_
          refine ENNReal.mul_ne_top (by simp) ?_
          simp only [K2]
          refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp) ?_, ENNReal.ofReal_ne_top⟩
          exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _)
      _ = (ENNReal.ofReal m⁻¹ * (4 * K2 n q q₀ A)) ^ q * (ENNReal.ofReal (c ^ n) * ∫⁻ x, ‖f x‖ₑ ^ q) := by
          rw [← lintegral_tile (R := R) (fun x => ‖f x‖ₑ ^ q)
            (hf.measurable.enorm.pow_const _)]
          · rw [ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal m⁻¹) (4 * K2 n q q₀ A) hq0.le]; ring
          · intro x hx; apply hF x; intro h; apply hx; simp [h, hq0]
  calc (∫⁻ ω, ‖restriction f ω‖ₑ ^ q ∂(sphereMeasure n)) ^ (1 / q)
      ≤ ((ENNReal.ofReal m⁻¹ * (4 * K2 n q q₀ A)) ^ q * (ENNReal.ofReal (c ^ n) * ∫⁻ x, ‖f x‖ₑ ^ q)) ^ (1 / q) :=
        ENNReal.rpow_le_rpow key (by positivity)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg ((ENNReal.ofReal m⁻¹ * (4 * K2 n q q₀ A)) ^ q) _
            (by positivity),
          ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal (c ^ n)) _ (by positivity),
          ← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
        ring

end Main

end TaoBR.CU

end
end

section
section
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace SchwartzMap

namespace TaoBR

open CU

theorem restr_zero_of_cubeUnion_bound_dev (n : ℕ) (hn : 2 ≤ n) (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (q₀ : ℝ) (hq₀ : 1 < q₀) (hq₀p : q₀ ≤ p) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (h : ∃ C : ℝ, ∀ S : Set (E n), IsCubeUnion c S →
      eLpNorm (restriction (S.indicator fun _ => (1 : ℂ))) (ENNReal.ofReal p) (sphereMeasure n) ≤
        ENNReal.ofReal (C * (volume S).toReal ^ (1 / q₀))) :
    ∀ q : ℝ≥0∞, 1 ≤ q → q < ENNReal.ofReal q₀ → Restr n q 0 := by
  intro q hq1 hqlt
  obtain ⟨C, hC⟩ := h
  have hqtop : q ≠ ⊤ := ne_top_of_lt hqlt
  set qr := q.toReal with hqrdef
  have hqe : ENNReal.ofReal qr = q := ENNReal.ofReal_toReal hqtop
  have hqr1 : 1 ≤ qr := by
    have := ENNReal.toReal_mono hqtop hq1; simpa using this
  have hqrq : qr < q₀ := (ENNReal.lt_ofReal_iff_toReal_lt hqtop).mp hqlt
  have hqr0 : 0 < qr := by linarith
  set σu := sphereMeasure n Set.univ with hσu
  have hσtop : σu ≠ ⊤ := measure_ne_top _ _
  set e := 1 / qr - 1 / p with he
  have he0 : 0 ≤ e := by
    rw [he, sub_nonneg]; exact one_div_le_one_div_of_le (by linarith) (by linarith)
  set A := max C 0 * σu.toReal ^ e with hAdef
  have hA : 0 ≤ A := mul_nonneg (le_max_right _ _) (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  have h4 : ∀ t : Finset (Fin n → ℤ), eLpNorm (cubeSum c t (fun _ => 1)) (ENNReal.ofReal qr)
      (sphereMeasure n) ≤ ENNReal.ofReal (A * ((t.card : ℝ) * c ^ n) ^ (1 / q₀)) := by
    intro t
    have h1 := hC (⋃ k ∈ t, cCube c k) ⟨t, rfl⟩
    rw [restriction_iUnion hc1 t, volume_iUnion_cCube hc.le hc1 t] at h1
    have hV : ((t.card : ℝ≥0∞) * ENNReal.ofReal c ^ n).toReal = (t.card : ℝ) * c ^ n := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hc.le]; simp
    rw [hV] at h1
    have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := sphereMeasure n)
      (p := ENNReal.ofReal qr) (q := ENNReal.ofReal p)
      (ENNReal.ofReal_le_ofReal (by linarith)) (aesm_cubeSum c t (fun _ => 1))
    rw [ENNReal.toReal_ofReal hqr0.le, ENNReal.toReal_ofReal (by linarith)] at h2
    refine h2.trans ?_
    have hσe : σu ^ (1 / qr - 1 / p) = ENNReal.ofReal (σu.toReal ^ e) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg he0, ENNReal.ofReal_toReal hσtop]
    rw [← hσu, hσe]
    calc eLpNorm (cubeSum c t fun _ => 1) (ENNReal.ofReal p) (sphereMeasure n) *
          ENNReal.ofReal (σu.toReal ^ e)
        ≤ ENNReal.ofReal (max C 0 * ((t.card : ℝ) * c ^ n) ^ (1 / q₀)) *
          ENNReal.ofReal (σu.toReal ^ e) := by
          gcongr
          refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
          gcongr; exact le_max_left _ _
      _ = ENNReal.ofReal (A * ((t.card : ℝ) * c ^ n) ^ (1 / q₀)) := by
          rw [← ENNReal.ofReal_mul (by positivity), hAdef]; ring_nf
  obtain ⟨m, hm0, hm⟩ := exists_lower_bound_phi (n := n) hc hc1
  set Kc : ℝ≥0∞ := ENNReal.ofReal m⁻¹ * (4 * K2 n qr q₀ A) * ENNReal.ofReal (c ^ n) ^ (1 / qr)
  have hKc : Kc ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (by simp) ?_)) (ENNReal.rpow_ne_top_of_nonneg (by positivity)
        ENNReal.ofReal_ne_top)
    simp only [K2]
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp) ?_, ENNReal.ofReal_ne_top⟩
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hσtop
  refine ⟨Kc.toNNReal, fun R hR f hf => ?_⟩
  rw [Real.rpow_zero, ENNReal.ofReal_one, mul_one, ENNReal.coe_toNNReal hKc,
    eLpNorm_restrict_eq_of_support_subset ((subset_tsupport _).trans hf), ← hqe]
  refine restriction_eLpNorm_le hc hqr1 hqrq hA h4 hm0 hm (R := R) f f.continuous f.integrable ?_
  intro x hx
  have := hf (subset_tsupport _ (Function.mem_support.mpr hx))
  rwa [mem_closedBall_zero_iff] at this

end TaoBR

end
end

section
open MeasureTheory
open scoped ENNReal
open TaoBR

theorem solution (n : ℕ) (hn : 2 ≤ n) (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (q₀ : ℝ) (hq₀ : 1 < q₀) (hq₀p : q₀ ≤ p) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (h : ∃ C : ℝ, ∀ S : Set (E n), IsCubeUnion c S →
      eLpNorm (restriction (S.indicator fun _ => (1 : ℂ))) (ENNReal.ofReal p) (sphereMeasure n) ≤
        ENNReal.ofReal (C * (volume S).toReal ^ (1 / q₀))) :
    ∀ q : ℝ≥0∞, 1 ≤ q → q < ENNReal.ofReal q₀ → Restr n q 0 := by
  exact TaoBR.restr_zero_of_cubeUnion_bound_dev n hn p hp hp2 q₀ hq₀ hq₀p c hc hc1 h

end
