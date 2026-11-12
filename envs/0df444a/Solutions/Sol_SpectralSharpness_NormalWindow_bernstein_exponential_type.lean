-- Prove2me | solution 1 for SpectralSharpness.NormalWindow.bernstein_exponential_type
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T21:57:45.658473+00:00
-- url     : https://prove2.me/submissions/a119618f-c50c-4000-8054-f94b30af72a1

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_ExponentialType

section
set_option autoImplicit false

namespace SpectralSharpness.Dev.Bern

/-- Riesz node `(k + 1/2) π / σ`. -/
noncomputable def node (σ : ℝ) (k : ℤ) : ℂ := ((k : ℂ) + 1 / 2) * ((Real.pi : ℂ) / (σ : ℂ))

/-- residue of `f z / (z^2 cos (σ z))` at the node `node σ k`. -/
noncomputable def coef (σ : ℝ) (f : ℂ → ℂ) (k : ℤ) : ℂ :=
  f (node σ k) / ((node σ k) ^ 2 * (-(σ : ℂ) * Complex.sin ((σ : ℂ) * node σ k)))

end SpectralSharpness.Dev.Bern
end

section
set_option autoImplicit false

open Complex

namespace SpectralSharpness.Dev.BernCos

lemma norm_cos_sq (w : ℂ) :
    ‖Complex.cos w‖ ^ 2 = Real.cos w.re ^ 2 + Real.sinh w.im ^ 2 := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have h1 : Complex.cos w = ((Real.cos w.re * Real.cosh w.im : ℝ) : ℂ) +
      ((-(Real.sin w.re * Real.sinh w.im) : ℝ) : ℂ) * Complex.I := by
    conv_lhs => rw [hw, Complex.cos_add_mul_I]
    push_cast
    simp [Complex.ofReal_cos, Complex.ofReal_sin, Complex.ofReal_cosh, Complex.ofReal_sinh]
    ring
  rw [h1, Complex.sq_norm, Complex.normSq_add_mul_I]
  have := Real.cosh_sq w.im
  have h2 := Real.sin_sq_add_cos_sq w.re
  nlinarith [this, h2]

lemma cos_lower (m : ℕ) (hm : 1 ≤ m) (w : ℂ) (hw : ‖w‖ = m * Real.pi) :
    Real.exp |w.im| / 4 ≤ ‖Complex.cos w‖ := by
  have hsq := norm_cos_sq w
  have hn : w.re ^ 2 + w.im ^ 2 = (m * Real.pi) ^ 2 := by
    have := Complex.sq_norm w
    rw [Complex.normSq_apply] at this
    rw [hw] at this
    nlinarith [this]
  have hpi := Real.pi_gt_three
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  by_cases hb : 1 ≤ |w.im|
  · -- large imaginary part: sinh dominates
    have h1 : Real.exp |w.im| / 4 ≤ |Real.sinh w.im| := by
      have : |Real.sinh w.im| = Real.sinh |w.im| := Real.abs_sinh _
      rw [this, Real.sinh_eq]
      have h2 : Real.exp (-|w.im|) * Real.exp |w.im| = 1 := by
        rw [← Real.exp_add]; simp
      have h3 : 2 ≤ Real.exp |w.im| * Real.exp |w.im| := by
        have : Real.exp 1 ≤ Real.exp |w.im| := Real.exp_le_exp.mpr hb
        have h4 : 2 ≤ Real.exp 1 := by
          have := Real.add_one_le_exp (1 : ℝ); linarith
        nlinarith [Real.exp_pos |w.im|]
      have hpos := Real.exp_pos |w.im|
      have hneg := Real.exp_pos (-|w.im|)
      nlinarith [h2, h3, hpos, hneg]
    have h5 : |Real.sinh w.im| ≤ ‖Complex.cos w‖ := by
      refine (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp ?_
      rw [sq_abs, hsq]; nlinarith [sq_nonneg (Real.cos w.re)]
    linarith
  · push_neg at hb
    -- small imaginary part: the real part is close to a multiple of pi
    have hb2 : w.im ^ 2 < 1 := by
      have := sq_abs w.im
      nlinarith [abs_nonneg w.im]
    have hare : |w.re| ≤ m * Real.pi := by
      refine (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp ?_
      rw [sq_abs]; nlinarith [sq_nonneg w.im]
    set δ := m * Real.pi - |w.re| with hδ
    have hδ0 : 0 ≤ δ := by linarith
    have hδ1 : δ ≤ 1 / 3 := by
      have : δ * (m * Real.pi + |w.re|) = w.im ^ 2 := by
        have := sq_abs w.re
        nlinarith [hn, this]
      have hmp : 3 ≤ m * Real.pi + |w.re| := by nlinarith [abs_nonneg w.re]
      nlinarith
    have hcos : Real.cos w.re ^ 2 = Real.cos δ ^ 2 := by
      have h1 : Real.cos w.re = Real.cos |w.re| := by
        rw [Real.cos_abs]
      have h2 : Real.cos |w.re| = Real.cos ((m : ℝ) * Real.pi - δ) := by
        congr 1; rw [hδ]; ring
      rw [h1, h2, Real.cos_nat_mul_pi_sub]
      rw [mul_pow, ← pow_mul]
      have : ((-1 : ℝ) ^ (m * 2)) = 1 := by rw [pow_mul']; simp
      rw [this, one_mul]
    have hcd : 8 / 9 ≤ Real.cos δ ^ 2 := by
      have h1 := Real.sin_sq_add_cos_sq δ
      have h2 : Real.sin δ ≤ δ := Real.sin_le hδ0
      have h3 : 0 ≤ Real.sin δ := Real.sin_nonneg_of_nonneg_of_le_pi hδ0 (by linarith)
      nlinarith
    have he : Real.exp |w.im| < 2.7182818286 := by
      have := Real.exp_one_lt_d9
      calc Real.exp |w.im| ≤ Real.exp 1 := Real.exp_le_exp.mpr hb.le
        _ < _ := this
    have hsq' : (Real.exp |w.im| / 4) ^ 2 ≤ ‖Complex.cos w‖ ^ 2 := by
      have := Real.exp_pos |w.im|
      nlinarith [sq_nonneg (Real.sinh w.im)]
    exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) (by norm_num)).mp hsq'

end SpectralSharpness.Dev.BernCos
end

section
set_option autoImplicit false

open Complex

namespace SpectralSharpness.Dev.BernA

open Filter Topology in
theorem upper_half (σ M : ℝ) (hσ : 0 < σ) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hexp : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp ((σ + ε) * ‖z‖))
    (hM : ∀ x : ℝ, ‖f (x : ℂ)‖ ≤ M) (ε : ℝ) (hε : 0 < ε) (z : ℂ) (hz : 0 ≤ z.im) :
    ‖f z‖ ≤ M * Real.exp ((σ + ε) * z.im) := by
  obtain ⟨C, hC⟩ := hexp (ε / 2) (by positivity)
  have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  set G : ℂ → ℂ := fun w => f (I * w) * Complex.exp (-(((σ + ε : ℝ) : ℂ) * w)) with hG
  have hGd : Differentiable ℂ G := by
    apply Differentiable.mul
    · exact hf.comp (differentiable_const _ |>.mul differentiable_id)
    · fun_prop
  have hGn : ∀ w, ‖G w‖ = ‖f (I * w)‖ * Real.exp (-((σ + ε) * w.re)) := by
    intro w
    simp only [hG, norm_mul, Complex.norm_exp]
    congr 2
    simp
  have key := PhragmenLindelof.right_half_plane_of_bounded_on_real (f := G) (C := M)
    (z := -I * z) hGd.diffContOnCl ?_ ?_ ?_ (by simpa using hz)
  · have h := key
    rw [hGn] at h
    have e : I * (-I * z) = z := by
      rw [← mul_assoc]; simp
    rw [e] at h
    have e2 : (-I * z).re = z.im := by simp
    rw [e2] at h
    have hp := Real.exp_pos ((σ + ε) * z.im)
    have : ‖f z‖ = ‖f z‖ * Real.exp (-((σ + ε) * z.im)) * Real.exp ((σ + ε) * z.im) := by
      rw [mul_assoc, ← Real.exp_add]; simp
    rw [this]
    exact mul_le_mul_of_nonneg_right h hp.le
  · refine ⟨1, by norm_num, σ + ε, ?_⟩
    refine Asymptotics.IsBigO.of_bound C ?_
    refine eventually_inf_principal.2 <| Eventually.of_forall fun w hw => ?_
    have hw' : 0 < w.re := hw
    rw [hGn, Real.norm_eq_abs, Real.rpow_one, abs_of_pos (Real.exp_pos _)]
    have h1 := hC (I * w)
    rw [norm_mul, Complex.norm_I, one_mul] at h1
    have h2 : Real.exp (-((σ + ε) * w.re)) ≤ 1 := by
      apply Real.exp_le_one_iff.2; nlinarith
    have h3 : Real.exp ((σ + ε / 2) * ‖w‖) ≤ Real.exp ((σ + ε) * ‖w‖) :=
      Real.exp_le_exp.2 (by nlinarith [norm_nonneg w])
    calc ‖f (I * w)‖ * Real.exp (-((σ + ε) * w.re))
        ≤ (C * Real.exp ((σ + ε / 2) * ‖w‖)) * 1 :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
      _ ≤ C * Real.exp ((σ + ε) * ‖w‖) := by rw [mul_one]; exact mul_le_mul_of_nonneg_left h3 hC0
  · refine Filter.isBoundedUnder_of_eventually_le (a := C) ((Filter.eventually_ge_atTop (0:ℝ)).mono fun x hx => ?_)
    rw [hGn]
    have h1 := hC (I * (x:ℂ))
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at h1
    simp only [Complex.ofReal_re]
    rw [abs_of_nonneg hx] at h1
    calc ‖f (I * x)‖ * Real.exp (-((σ + ε) * x))
        ≤ (C * Real.exp ((σ + ε / 2) * x)) * Real.exp (-((σ + ε) * x)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = C * Real.exp (-(ε / 2 * x)) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (by nlinarith)) hC0
      _ = C := mul_one _
  · intro x
    rw [hGn]
    have : (↑x * I : ℂ).re = 0 := by simp
    rw [this]
    have e : I * (↑x * I) = ((-x : ℝ) : ℂ) := by
      push_cast; rw [mul_comm (x:ℂ), ← mul_assoc]; simp
    rw [e]; simpa using hM (-x)

/-- Part A (Phragmen-Lindelof): sharp growth bound. -/
theorem growth_bound (σ M : ℝ) (hσ : 0 < σ) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hexp : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp ((σ + ε) * ‖z‖))
    (hM : ∀ x : ℝ, ‖f (x : ℂ)‖ ≤ M) :
    ∀ z : ℂ, ‖f z‖ ≤ M * Real.exp (σ * |z.im|) := by
  intro z
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hf' : Differentiable ℂ (fun z => f (-z)) := hf.comp differentiable_neg
  have hexp' : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ z : ℂ,
      ‖f (-z)‖ ≤ C * Real.exp ((σ + ε) * ‖z‖) := by
    intro ε hε
    obtain ⟨C, hC⟩ := hexp ε hε
    exact ⟨C, fun z => by simpa using hC (-z)⟩
  have hM' : ∀ x : ℝ, ‖f (-(x : ℂ))‖ ≤ M := fun x => by
    simpa using hM (-x)
  have hε : ∀ ε : ℝ, 0 < ε → ‖f z‖ ≤ M * Real.exp ((σ + ε) * |z.im|) := by
    intro ε hε
    rcases le_total 0 z.im with h | h
    · rw [abs_of_nonneg h]; exact upper_half σ M hσ f hf hexp hM ε hε z h
    · rw [abs_of_nonpos h]
      have := upper_half σ M hσ (fun z => f (-z)) hf' hexp' hM' ε hε (-z) (by simpa using h)
      simpa using this
  have hlim : Filter.Tendsto (fun ε : ℝ => M * Real.exp ((σ + ε) * |z.im|))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (M * Real.exp (σ * |z.im|))) := by
    have : Continuous (fun ε : ℝ => M * Real.exp ((σ + ε) * |z.im|)) := by fun_prop
    have h2 := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using h2
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε' => hε ε hε')

end SpectralSharpness.Dev.BernA
end

section
set_option autoImplicit false

open Complex Filter Topology Asymptotics Metric Set

namespace SpectralSharpness.Dev.BernB1
open SpectralSharpness.Dev.Bern

lemma isLittleO_of_tendsto_mul (g : ℂ → ℂ) (p : ℂ)
    (h : Tendsto (fun z => (z - p) * g z) (𝓝[≠] p) (𝓝 0)) :
    (fun z => g z - g p) =o[𝓝[≠] p] fun z => (z - p)⁻¹ := by
  have h0 : Tendsto (fun z => (z - p) * (g z - g p)) (𝓝[≠] p) (𝓝 0) := by
    have h1 : Tendsto (fun z : ℂ => (z - p) * g p) (𝓝[≠] p) (𝓝 0) := by
      have : Tendsto (fun z : ℂ => (z - p) * g p) (𝓝 p) (𝓝 ((p - p) * g p)) :=
        (((continuous_id.sub continuous_const).mul continuous_const).tendsto p)
      simpa using this.mono_left nhdsWithin_le_nhds
    simpa [mul_sub] using h.sub h1
  have h2 : (fun z => (z - p) * (g z - g p)) =o[𝓝[≠] p] (fun _ => (1:ℂ)) :=
    (isLittleO_one_iff ℂ).2 h0
  have h3 := h2.mul_isBigO (Asymptotics.isBigO_refl (fun z : ℂ => (z - p)⁻¹) (𝓝[≠] p))
  refine h3.congr' ?_ (Eventually.of_forall fun z => by simp)
  filter_upwards [self_mem_nhdsWithin] with z hz
  have : z - p ≠ 0 := sub_ne_zero.2 hz
  field_simp

lemma removable_finset (U : Set ℂ) (hU : IsOpen U) (P : Finset ℂ) (g : ℂ → ℂ)
    (hd : ∀ z ∈ U, z ∉ P → DifferentiableAt ℂ g z)
    (ho : ∀ p ∈ P, Tendsto (fun z => (z - p) * g z) (𝓝[≠] p) (𝓝 0)) :
    ∃ E : ℂ → ℂ, DifferentiableOn ℂ E U ∧ ∀ z, z ∉ P → E z = g z := by
  classical
  refine ⟨fun z => if z ∈ P then limUnder (𝓝[≠] z) g else g z, ?_, ?_⟩
  · intro z hz
    apply DifferentiableAt.differentiableWithinAt
    by_cases hzP : z ∈ P
    · set s : Set ℂ := U ∩ (↑(P.erase z) : Set ℂ)ᶜ with hs
      have hsn : s ∈ 𝓝 z := by
        apply Filter.inter_mem (hU.mem_nhds hz)
        exact (P.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
      have hdiff : DifferentiableOn ℂ g (s \ {z}) := by
        intro w hw
        apply DifferentiableAt.differentiableWithinAt
        apply hd w hw.1.1
        intro hwP
        have : w ∈ P.erase z := Finset.mem_erase.2 ⟨by simpa using hw.2, hwP⟩
        exact hw.1.2 this
      have := Complex.differentiableOn_update_limUnder_of_isLittleO hsn hdiff
        (isLittleO_of_tendsto_mul g z (ho z hzP))
      refine ((this.congr ?_).differentiableAt hsn)
      intro w hw
      by_cases hwz : w = z
      · subst hwz; simp [hzP]
      · have hwP : w ∉ P := fun h => hw.2 (by simp [hwz, h])
        simp [hwP, hwz]
    · have hPc : (↑P : Set ℂ)ᶜ ∈ 𝓝 z := P.finite_toSet.isClosed.isOpen_compl.mem_nhds (by simpa using hzP)
      have hdz := hd z hz hzP
      refine hdz.congr_of_eventuallyEq ?_
      filter_upwards [hPc] with w hw
      have : w ∉ P := by simpa using hw
      simp [this]
  · intro z hz; simp [hz]


lemma node_eq (σ : ℝ) (k : ℤ) : node σ k = (((k : ℝ) + 1 / 2) * (Real.pi / σ) : ℝ) := by
  simp [node]

lemma node_ne_zero (σ : ℝ) (hσ : 0 < σ) (k : ℤ) : node σ k ≠ 0 := by
  rw [node_eq]
  have h1 : ((k : ℝ) + 1 / 2) ≠ 0 := by
    intro h
    have : (2 * k + 1 : ℝ) = 0 := by linarith
    have h2 : (2 * k + 1 : ℤ) = 0 := by exact_mod_cast this
    omega
  have : ((k : ℝ) + 1 / 2) * (Real.pi / σ) ≠ 0 := mul_ne_zero h1 (by positivity)
  exact_mod_cast this

lemma node_inj (σ : ℝ) (hσ : 0 < σ) {j k : ℤ} (h : node σ j = node σ k) : j = k := by
  rw [node_eq, node_eq] at h
  have h' : ((j : ℝ) + 1 / 2) * (Real.pi / σ) = ((k : ℝ) + 1 / 2) * (Real.pi / σ) := by
    exact_mod_cast h
  have hp : Real.pi / σ ≠ 0 := by positivity
  have := mul_right_cancel₀ hp h'
  exact_mod_cast (by linarith : (j : ℝ) = k)

lemma cos_node (σ : ℝ) (hσ : 0 < σ) (k : ℤ) : Complex.cos ((σ : ℂ) * node σ k) = 0 := by
  rw [Complex.cos_eq_zero_iff]
  refine ⟨k, ?_⟩
  have : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  simp only [node]
  field_simp

lemma exists_node (σ : ℝ) (hσ : 0 < σ) {z : ℂ} (h : Complex.cos ((σ : ℂ) * z) = 0) :
    ∃ k : ℤ, z = node σ k := by
  rw [Complex.cos_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  simp only [node]
  field_simp
  linear_combination 2 * hk

lemma sin_node_ne (σ : ℝ) (hσ : 0 < σ) (k : ℤ) : Complex.sin ((σ : ℂ) * node σ k) ≠ 0 := by
  intro h
  have := Complex.sin_sq_add_cos_sq ((σ : ℂ) * node σ k)
  rw [h, cos_node σ hσ k] at this
  simp at this

lemma abs_node (σ : ℝ) (hσ : 0 < σ) (k : ℤ) : ‖node σ k‖ = |(k : ℝ) + 1 / 2| * (Real.pi / σ) := by
  rw [node_eq, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < Real.pi / σ)]


noncomputable def Psi (σ : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z / (z ^ 2 * Complex.cos ((σ : ℂ) * z))

noncomputable def Ssing (σ : ℝ) (f : ℂ → ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  f 0 / z ^ 2 + deriv f 0 / z + ∑ k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), coef σ f k / (z - node σ k)

noncomputable def Gg (σ : ℝ) (f : ℂ → ℂ) (m : ℕ) (z : ℂ) : ℂ := Psi σ f z - Ssing σ f m z

lemma tendsto_simple (σ : ℝ) (hσ : 0 < σ) (f : ℂ → ℂ) (hf : Differentiable ℂ f) (k : ℤ) :
    Tendsto (fun z => (z - node σ k) * Psi σ f z) (𝓝[≠] node σ k) (𝓝 (coef σ f k)) := by
  set p := node σ k with hp
  have hp0 : p ≠ 0 := node_ne_zero σ hσ k
  have hc : HasDerivAt (fun z : ℂ => Complex.cos ((σ : ℂ) * z)) (-Complex.sin ((σ : ℂ) * p) * (σ : ℂ)) p := by
    have := ((hasDerivAt_id p).const_mul (σ : ℂ)).ccos
    simpa using this
  have hs := (hasDerivAt_iff_tendsto_slope.1 hc)
  have hd : -Complex.sin ((σ : ℂ) * p) * (σ : ℂ) ≠ 0 := by
    have : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
    exact mul_ne_zero (neg_ne_zero.2 (sin_node_ne σ hσ k)) this
  have h1 := hs.inv₀ hd
  have h2 : Tendsto (fun z => f z / z ^ 2) (𝓝[≠] p) (𝓝 (f p / p ^ 2)) := by
    have : ContinuousAt (fun z => f z / z ^ 2) p :=
      hf.continuous.continuousAt.div (continuous_id.pow 2).continuousAt (pow_ne_zero 2 hp0)
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have h3 := h2.mul h1
  have h4 : f p / p ^ 2 * (-Complex.sin ((σ : ℂ) * p) * (σ : ℂ))⁻¹ = coef σ f k := by
    simp only [coef, ← hp]
    field_simp
  rw [h4] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have : z - p ≠ 0 := sub_ne_zero.2 hz
  simp only [slope_def_field, Psi]
  have hcp : Complex.cos ((σ : ℂ) * p) = 0 := cos_node σ hσ k
  rw [hcp]
  simp only [sub_zero, inv_div]
  ring


lemma tendsto_S_simple (σ : ℝ) (hσ : 0 < σ) (f : ℂ → ℂ) (m : ℕ) (k : ℤ)
    (hk : k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ)) :
    Tendsto (fun z => (z - node σ k) * Ssing σ f m z) (𝓝[≠] node σ k) (𝓝 (coef σ f k)) := by
  set p := node σ k with hp
  have hp0 : p ≠ 0 := node_ne_zero σ hσ k
  have hA : Tendsto (fun z : ℂ => (z - p) * (f 0 / z ^ 2 + deriv f 0 / z)) (𝓝[≠] p) (𝓝 0) := by
    have : ContinuousAt (fun z : ℂ => (z - p) * (f 0 / z ^ 2 + deriv f 0 / z)) p := by
      apply ContinuousAt.mul (continuousAt_id.sub continuousAt_const)
      exact (continuousAt_const.div (continuous_id.pow 2).continuousAt (pow_ne_zero 2 hp0)).add
        (continuousAt_const.div continuousAt_id hp0)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have hB : Tendsto (fun z : ℂ => ∑ j ∈ Finset.Ico (-(m : ℤ)) (m : ℤ),
      coef σ f j * ((z - p) / (z - node σ j))) (𝓝[≠] p)
      (𝓝 (∑ j ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), (if j = k then coef σ f j else 0))) := by
    apply tendsto_finsetSum
    intro j _
    by_cases hjk : j = k
    · subst hjk
      simp only [if_true]
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      have : z - node σ j ≠ 0 := sub_ne_zero.2 hz
      field_simp
      rw [hp]
    · simp only [hjk, if_false]
      have hne : p - node σ j ≠ 0 := sub_ne_zero.2 (fun h => hjk (node_inj σ hσ h.symm))
      have : ContinuousAt (fun z : ℂ => coef σ f j * ((z - p) / (z - node σ j))) p :=
        continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).div
          (continuousAt_id.sub continuousAt_const) hne)
      simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have h5 := hA.add hB
  rw [Finset.sum_ite_eq' (Finset.Ico (-(m : ℤ)) (m : ℤ)) k, if_pos hk] at h5
  simp only [zero_add] at h5
  refine h5.congr' ?_
  filter_upwards with z
  simp only [Ssing]
  rw [mul_add (z - p) (f 0 / z ^ 2 + deriv f 0 / z), Finset.mul_sum, mul_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma tendsto_g_simple (σ : ℝ) (hσ : 0 < σ) (f : ℂ → ℂ) (hf : Differentiable ℂ f) (m : ℕ) (k : ℤ)
    (hk : k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ)) :
    Tendsto (fun z => (z - node σ k) * Gg σ f m z) (𝓝[≠] node σ k) (𝓝 0) := by
  have := (tendsto_simple σ hσ f hf k).sub (tendsto_S_simple σ hσ f m k hk)
  simp only [sub_self] at this
  refine this.congr' ?_
  filter_upwards with z
  simp only [Gg]
  ring

lemma tendsto_g_zero (σ : ℝ) (hσ : 0 < σ) (f : ℂ → ℂ) (hf : Differentiable ℂ f) (m : ℕ) :
    Tendsto (fun z => (z - 0) * Gg σ f m z) (𝓝[≠] 0) (𝓝 0) := by
  have hF : HasDerivAt (fun z : ℂ => f z / Complex.cos ((σ : ℂ) * z)) (deriv f 0) 0 := by
    have hc : HasDerivAt (fun z : ℂ => Complex.cos ((σ : ℂ) * z)) (-Complex.sin ((σ : ℂ) * 0) * (σ : ℂ)) 0 := by
      have := ((hasDerivAt_id (0:ℂ)).const_mul (σ : ℂ)).ccos
      simpa using this
    have h := (hf.differentiableAt.hasDerivAt (x := 0)).div hc (by simp)
    have e : (deriv f 0 * Complex.cos ((σ : ℂ) * 0) - f 0 * (-Complex.sin ((σ : ℂ) * 0) * (σ : ℂ))) /
        Complex.cos ((σ : ℂ) * 0) ^ 2 = deriv f 0 := by simp
    rw [e] at h
    exact h
  have hs := hasDerivAt_iff_tendsto_slope.1 hF
  have hs2 : Tendsto (fun z : ℂ => z⁻¹ * (f z / Complex.cos ((σ : ℂ) * z) - f 0) - deriv f 0)
      (𝓝[≠] 0) (𝓝 0) := by
    have := hs.sub_const (deriv f 0)
    simp only [sub_self] at this
    refine this.congr' ?_
    filter_upwards with z
    simp [slope_def_field, div_eq_inv_mul]
  have hB : Tendsto (fun z : ℂ => z * ∑ k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), coef σ f k / (z - node σ k))
      (𝓝[≠] 0) (𝓝 0) := by
    have hsum : Tendsto (fun z : ℂ => ∑ k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), coef σ f k / (z - node σ k))
        (𝓝 0) (𝓝 (∑ k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), coef σ f k / (0 - node σ k))) := by
      apply tendsto_finsetSum
      intro k _
      exact (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
        (by simpa using node_ne_zero σ hσ k)).tendsto
    have := (tendsto_id (α := ℂ)).mul hsum
    simpa using this.mono_left nhdsWithin_le_nhds
  have h6 := hs2.sub hB
  simp only [sub_zero, sub_self] at h6 ⊢
  refine h6.congr' ?_
  have hev : ∀ᶠ z in 𝓝 (0:ℂ), Complex.cos ((σ : ℂ) * z) ≠ 0 :=
    (Complex.continuous_cos.comp (continuous_const.mul continuous_id)).continuousAt.eventually_ne
      (by simp)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hev] with z hz hc
  have hz0 : z ≠ 0 := hz
  simp only [Gg, Psi, Ssing]
  field_simp
  ring


lemma node_mem_Ico_of_lt (σ : ℝ) (hσ : 0 < σ) (m : ℕ) (k : ℤ)
    (h : ‖node σ k‖ < ((m : ℝ) + 1 / 2) * (Real.pi / σ)) : k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ) := by
  rw [abs_node σ hσ] at h
  have hq : 0 < Real.pi / σ := by positivity
  have h2 := lt_of_mul_lt_mul_right h hq.le
  rw [abs_lt] at h2
  obtain ⟨h3, h4⟩ := h2
  have h5 : (-(m : ℤ) : ℝ) - 1 < k := by push_cast; linarith
  have h6 : (k : ℝ) < m := by linarith
  have h7 : -(m : ℤ) - 1 < k := by exact_mod_cast h5
  have h8 : k < (m : ℤ) := by exact_mod_cast h6
  simp only [Finset.mem_Ico]
  omega

lemma node_norm_lt (σ : ℝ) (hσ : 0 < σ) (m : ℕ) (k : ℤ) (hk : k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ)) :
    ‖node σ k‖ < (m : ℝ) * (Real.pi / σ) := by
  rw [abs_node σ hσ]
  have hq : 0 < Real.pi / σ := by positivity
  simp only [Finset.mem_Ico] at hk
  obtain ⟨h1, h2⟩ := hk
  have h3 : (-(m : ℤ) : ℝ) ≤ k := by exact_mod_cast h1
  have h4 : (k : ℝ) + 1 ≤ m := by exact_mod_cast h2
  push_cast at h3
  apply mul_lt_mul_of_pos_right _ hq
  rw [abs_lt]; constructor <;> linarith

lemma node_norm_ne (σ : ℝ) (hσ : 0 < σ) (m : ℕ) (k : ℤ) :
    ‖node σ k‖ ≠ (m : ℝ) * (Real.pi / σ) := by
  rw [abs_node σ hσ]
  have hq : 0 < Real.pi / σ := by positivity
  intro h
  have h2 := mul_right_cancel₀ hq.ne' h
  rcases abs_cases ((k : ℝ) + 1 / 2) with ⟨h3, _⟩ | ⟨h3, _⟩
  · rw [h3] at h2
    have : (2 * k + 1 : ℝ) = 2 * m := by linarith
    have h4 : (2 * k + 1 : ℤ) = 2 * m := by exact_mod_cast this
    omega
  · rw [h3] at h2
    have : (2 * k + 1 : ℝ) = -(2 * m) := by linarith
    have h4 : (2 * k + 1 : ℤ) = -(2 * m) := by exact_mod_cast this
    omega

lemma ci_inv (c w : ℂ) (R : ℝ) (hR : 0 ≤ R) (hw : w ∉ Metric.sphere (0 : ℂ) R) :
    CircleIntegrable (fun z => c * (z - w)⁻¹) 0 R := by
  apply ContinuousOn.circleIntegrable hR
  exact continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).inv₀
    (fun z hz => sub_ne_zero.2 (fun h => by
      have h' : z = w := h
      exact hw (h' ▸ hz))))

lemma int_sum (R : ℝ) (hR : 0 ≤ R) (c : ℤ → ℂ) (w : ℤ → ℂ) (T : Finset ℤ)
    (hT : ∀ k ∈ T, w k ∈ Metric.ball (0 : ℂ) R) :
    (∮ z in C(0, R), ∑ k ∈ T, c k * (z - w k)⁻¹) = ∑ k ∈ T, c k * (2 * (Real.pi : ℂ) * Complex.I) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [circleIntegral]
  | insert a T ha ih =>
    have hT' : ∀ k ∈ T, w k ∈ Metric.ball (0 : ℂ) R := fun k hk => hT k (Finset.mem_insert_of_mem hk)
    have hnot : ∀ k ∈ insert a T, w k ∉ Metric.sphere (0 : ℂ) R := by
      intro k hk h
      have := hT k hk
      rw [Metric.mem_ball] at this
      rw [mem_sphere_iff_norm] at h
      simp only [sub_zero] at h
      rw [dist_zero_right] at this
      linarith
    simp only [Finset.sum_insert ha]
    have hs : CircleIntegrable (fun z => ∑ k ∈ T, c k * (z - w k)⁻¹) 0 R := by
      have := CircleIntegrable.sum T (c := (0:ℂ)) (R := R) (f := fun k z => c k * (z - w k)⁻¹)
        (fun k hk => ci_inv _ _ R hR (hnot k (Finset.mem_insert_of_mem hk)))
      convert this using 1
      ext z
      simp [Finset.sum_apply]
    rw [circleIntegral.integral_add (ci_inv _ _ R hR (hnot a (Finset.mem_insert_self _ _))) hs,
      ih hT', circleIntegral.integral_const_mul,
      circleIntegral.integral_sub_inv_of_mem_ball (hT a (Finset.mem_insert_self _ _))]


lemma Ssing_eq (σ : ℝ) (f : ℂ → ℂ) (m : ℕ) (z : ℂ) :
    Ssing σ f m z = f 0 * (z - 0) ^ (-2 : ℤ) + deriv f 0 * (z - 0)⁻¹ +
      ∑ k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), coef σ f k * (z - node σ k)⁻¹ := by
  simp [Ssing, zpow_neg, div_eq_mul_inv]

lemma int_Ssing (σ : ℝ) (hσ : 0 < σ) (f : ℂ → ℂ) (m : ℕ) (hm : 1 ≤ m) :
    (∮ z in C(0, (m : ℝ) * (Real.pi / σ)), Ssing σ f m z) =
      (2 * (Real.pi : ℂ) * Complex.I) * (deriv f 0 + ∑ k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), coef σ f k) := by
  set R : ℝ := (m : ℝ) * (Real.pi / σ) with hR
  have hq : 0 < Real.pi / σ := by positivity
  have hR0 : 0 < R := by
    have : (0:ℝ) < m := by exact_mod_cast hm
    positivity
  have hnodes : ∀ k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), node σ k ∈ Metric.ball (0 : ℂ) R := by
    intro k hk
    rw [mem_ball_zero_iff]
    exact node_norm_lt σ hσ m k hk
  have hnot : ∀ k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), node σ k ∉ Metric.sphere (0 : ℂ) R := by
    intro k hk h
    have := hnodes k hk
    rw [mem_ball_zero_iff] at this
    rw [mem_sphere_zero_iff_norm] at h
    linarith
  have h0ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by simpa using hR0
  have h0not : (0 : ℂ) ∉ Metric.sphere (0 : ℂ) R := by
    intro h
    rw [mem_sphere_zero_iff_norm] at h
    simp at h
    linarith
  have hc1 : CircleIntegrable (fun z : ℂ => f 0 * (z - 0) ^ (-2 : ℤ)) 0 R := by
    apply ContinuousOn.circleIntegrable hR0.le
    refine continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).zpow₀ _ ?_)
    intro z hz
    left
    refine sub_ne_zero.2 (fun h => h0not ?_)
    have h' : z = 0 := h
    exact h' ▸ hz
  have hc2 := ci_inv (deriv f 0) 0 R hR0.le h0not
  have hs : CircleIntegrable (fun z => ∑ k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), coef σ f k * (z - node σ k)⁻¹) 0 R := by
    have := CircleIntegrable.sum (Finset.Ico (-(m : ℤ)) (m : ℤ)) (c := (0:ℂ)) (R := R)
      (f := fun k z => coef σ f k * (z - node σ k)⁻¹)
      (fun k hk => ci_inv _ _ R hR0.le (hnot k hk))
    convert this using 1
    ext z
    simp [Finset.sum_apply]
  have e1 : (∮ z in C(0, R), Ssing σ f m z) = ∮ z in C(0, R), (f 0 * (z - 0) ^ (-2 : ℤ) + deriv f 0 * (z - 0)⁻¹ +
      ∑ k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), coef σ f k * (z - node σ k)⁻¹) := by
    congr 1; ext z; exact Ssing_eq σ f m z
  have h12 : CircleIntegrable (fun z : ℂ => f 0 * (z - 0) ^ (-2 : ℤ) + deriv f 0 * (z - 0)⁻¹) 0 R :=
    hc1.add hc2
  rw [e1, circleIntegral.integral_add h12 hs, circleIntegral.integral_add hc1 hc2,
    circleIntegral.integral_const_mul, circleIntegral.integral_sub_zpow_of_ne (by norm_num),
    circleIntegral.integral_const_mul, circleIntegral.integral_sub_inv_of_mem_ball h0ball,
    int_sum R hR0.le (coef σ f) (node σ) _ hnodes]
  rw [← Finset.sum_mul]
  ring


/-- Part B1 (residue identity on a circle through no pole). -/
theorem circle_residue (σ : ℝ) (hσ : 0 < σ) (f : ℂ → ℂ) (hf : Differentiable ℂ f) (m : ℕ)
    (hm : 1 ≤ m) :
    (∮ z in C(0, (m : ℝ) * Real.pi / σ), f z / (z ^ 2 * Complex.cos ((σ : ℂ) * z))) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (deriv f 0 + ∑ k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), coef σ f k) := by
  classical
  have hRe : (m : ℝ) * Real.pi / σ = (m : ℝ) * (Real.pi / σ) := by ring
  rw [hRe]
  set q : ℝ := Real.pi / σ with hqdef
  have hq : 0 < q := by positivity
  set R : ℝ := (m : ℝ) * q with hR
  have hR0 : 0 < R := by
    have : (0:ℝ) < m := by exact_mod_cast hm
    positivity
  set R' : ℝ := ((m : ℝ) + 1 / 2) * q with hR'
  have hRR' : R < R' := by rw [hR, hR']; nlinarith
  set P : Finset ℂ := insert 0 ((Finset.Ico (-(m : ℤ)) (m : ℤ)).image (node σ)) with hP
  -- the denominator is nonzero off P inside the big ball
  have hcos : ∀ z ∈ Metric.ball (0 : ℂ) R', z ∉ P → Complex.cos ((σ : ℂ) * z) ≠ 0 := by
    intro z hz hzP hc
    obtain ⟨k, rfl⟩ := exists_node σ hσ hc
    rw [mem_ball_zero_iff] at hz
    exact hzP (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (node_mem_Ico_of_lt σ hσ m k hz)))
  have hdiff : ∀ z ∈ Metric.ball (0 : ℂ) R', z ∉ P → DifferentiableAt ℂ (Gg σ f m) z := by
    intro z hz hzP
    have hz0 : z ≠ 0 := fun h => hzP (by simp [hP, h])
    have hc := hcos z hz hzP
    have hnk : ∀ k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), z - node σ k ≠ 0 := by
      intro k hk h
      exact hzP (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨k, hk, (sub_eq_zero.1 h).symm⟩))
    have h1 : DifferentiableAt ℂ (Psi σ f) z := by
      unfold Psi
      exact (hf.differentiableAt).div
        ((differentiableAt_id.pow 2).mul
          ((Complex.differentiableAt_cos).comp z (differentiableAt_const _ |>.mul differentiableAt_id)))
        (mul_ne_zero (pow_ne_zero 2 hz0) hc)
    have h2 : DifferentiableAt ℂ (Ssing σ f m) z := by
      unfold Ssing
      refine DifferentiableAt.add (DifferentiableAt.add ?_ ?_) ?_
      · exact (differentiableAt_const _).div (differentiableAt_id.pow 2) (pow_ne_zero 2 hz0)
      · exact (differentiableAt_const _).div differentiableAt_id hz0
      · refine DifferentiableAt.fun_sum ?_
        intro k hk
        exact (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _)) (hnk k hk)
    exact h1.sub h2
  have hlim : ∀ p ∈ P, Tendsto (fun z => (z - p) * Gg σ f m z) (𝓝[≠] p) (𝓝 0) := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp'
    · exact tendsto_g_zero σ hσ f hf m
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hp'
      exact tendsto_g_simple σ hσ f hf m k hk
  obtain ⟨E, hE, hEg⟩ := removable_finset (Metric.ball 0 R') Metric.isOpen_ball P (Gg σ f m) hdiff hlim
  have hsub : Metric.closedBall (0 : ℂ) R ⊆ Metric.ball 0 R' := Metric.closedBall_subset_ball hRR'
  have hE0 : (∮ z in C(0, R), E z) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hR0.le (Set.countable_empty)
      (hE.continuousOn.mono hsub)
      (fun z hz => (hE.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball hRR'.le hz.1))))
  have hsph : ∀ z ∈ Metric.sphere (0 : ℂ) R, z ∉ P := by
    intro z hz hzP
    rw [mem_sphere_zero_iff_norm] at hz
    rcases Finset.mem_insert.1 hzP with rfl | h
    · simp at hz; linarith
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 h
      exact node_norm_ne σ hσ m k hz
  have hG0 : (∮ z in C(0, R), Gg σ f m z) = 0 := by
    have := circleIntegral.integral_congr (c := 0) (f := Gg σ f m) (g := E) hR0.le
      (fun z hz => (hEg z (hsph z hz)).symm)
    rw [this]
    exact hE0
  have hPsi : CircleIntegrable (Psi σ f) 0 R := by
    apply ContinuousOn.circleIntegrable hR0.le
    intro z hz
    have hz0 : z ≠ 0 := fun h => hsph z hz (by simp [hP, h])
    have hc : Complex.cos ((σ : ℂ) * z) ≠ 0 := by
      intro hc
      obtain ⟨k, rfl⟩ := exists_node σ hσ hc
      rw [mem_sphere_zero_iff_norm] at hz
      exact node_norm_ne σ hσ m k hz
    unfold Psi
    refine ContinuousAt.continuousWithinAt ?_
    exact hf.continuous.continuousAt.div
      ((continuous_id.pow 2).mul (Complex.continuous_cos.comp (continuous_const.mul continuous_id))).continuousAt
      (mul_ne_zero (pow_ne_zero 2 hz0) hc)
  have hSi : CircleIntegrable (Ssing σ f m) 0 R := by
    apply ContinuousOn.circleIntegrable hR0.le
    intro z hz
    have hz0 : z ≠ 0 := fun h => hsph z hz (by simp [hP, h])
    have hnk : ∀ k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), z - node σ k ≠ 0 := by
      intro k hk h
      exact hsph z hz (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨k, hk, (sub_eq_zero.1 h).symm⟩))
    unfold Ssing
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.add (ContinuousAt.add ?_ ?_) ?_
    · exact continuousAt_const.div (continuous_id.pow 2).continuousAt (pow_ne_zero 2 hz0)
    · exact continuousAt_const.div continuousAt_id hz0
    · exact tendsto_finsetSum _ (fun k hk =>
        (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (hnk k hk)).tendsto)
  have hsplit : (∮ z in C(0, R), Psi σ f z) =
      (∮ z in C(0, R), Gg σ f m z) + ∮ z in C(0, R), Ssing σ f m z := by
    have : (∮ z in C(0, R), Psi σ f z) = ∮ z in C(0, R), (Gg σ f m z + Ssing σ f m z) := by
      congr 1; ext z; simp [Gg]
    rw [this]
    exact circleIntegral.integral_add (hPsi.sub hSi) hSi
  show (∮ z in C(0, R), Psi σ f z) = _
  rw [hsplit, hG0, zero_add, hR, hqdef]
  exact int_Ssing σ hσ f m hm

end SpectralSharpness.Dev.BernB1
end

section
set_option autoImplicit false

open Complex

namespace SpectralSharpness.Dev.BernRiesz
open SpectralSharpness.Dev.Bern SpectralSharpness.Dev

lemma hasSum_half_sq : HasSum (fun k : ℤ => 1 / (((k : ℝ) + 1 / 2) ^ 2)) (Real.pi ^ 2) := by
  have hz := hasSum_zeta_two
  have he : HasSum (fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 24) := by
    have := hz.mul_left (1 / 4 : ℝ)
    have e : (fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 2) = fun i : ℕ => 1 / 4 * (1 / (i : ℝ) ^ 2) := by
      funext k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · have : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
        push_cast; field_simp; norm_num
    rw [e, show Real.pi ^ 2 / 24 = 1 / 4 * (Real.pi ^ 2 / 6) by ring]
    exact this
  have hsum : Summable (fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2) :=
    hz.summable.comp_injective (i := fun k : ℕ => 2 * k + 1) (by intro a b h; simpa using h)
  have ho := hsum.hasSum
  have hall := HasSum.even_add_odd (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) he ho
  have hodd : (∑' k : ℕ, (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2) = Real.pi ^ 2 / 8 := by
    have := hall.unique hz
    linarith
  have hodd' : HasSum (fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 8) := by
    rw [← hodd]; exact ho
  have h1 : HasSum (fun k : ℕ => 1 / (((k : ℤ) : ℝ) + 1 / 2) ^ 2) (Real.pi ^ 2 / 2) := by
    have := hodd'.mul_left 4
    have e : (fun k : ℕ => 1 / (((k : ℤ) : ℝ) + 1 / 2) ^ 2) =
        fun k : ℕ => 4 * ((1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
      funext k; push_cast; field_simp; ring
    rw [e, show Real.pi ^ 2 / 2 = 4 * (Real.pi ^ 2 / 8) by ring]
    exact this
  have h2 : HasSum (fun k : ℕ => 1 / (((-((k : ℤ) + 1) : ℤ) : ℝ) + 1 / 2) ^ 2) (Real.pi ^ 2 / 2) := by
    have e : (fun k : ℕ => 1 / (((-((k : ℤ) + 1) : ℤ) : ℝ) + 1 / 2) ^ 2) =
        fun k : ℕ => 1 / (((k : ℤ) : ℝ) + 1 / 2) ^ 2 := by
      funext k; push_cast; ring_nf
    rw [e]; exact h1
  have := HasSum.of_nat_of_neg_add_one (f := fun k : ℤ => 1 / (((k : ℝ) + 1 / 2) ^ 2)) h1 h2
  rwa [show Real.pi ^ 2 / 2 + Real.pi ^ 2 / 2 = Real.pi ^ 2 by ring] at this

lemma norm_sin_node (σ : ℝ) (hσ : 0 < σ) (k : ℤ) :
    ‖Complex.sin ((σ : ℂ) * node σ k)‖ = 1 := by
  have h : (σ : ℂ) * node σ k = (((k : ℝ) + 1 / 2) * Real.pi : ℝ) := by
    unfold node; push_cast
    have : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
    field_simp
  rw [h, ← Complex.ofReal_sin, Complex.norm_real, Real.norm_eq_abs]
  have h1 : Real.sin (((k : ℝ) + 1 / 2) * Real.pi) = Real.cos ((k : ℝ) * Real.pi) := by
    rw [← Real.sin_add_pi_div_two]; congr 1; ring
  rw [h1]
  have h2 := Real.sin_sq_add_cos_sq ((k : ℝ) * Real.pi)
  have h3 : Real.sin ((k : ℝ) * Real.pi) = 0 := by
    have := Real.sin_int_mul_pi k; simpa using this
  rw [h3] at h2
  have : Real.cos ((k : ℝ) * Real.pi) ^ 2 = 1 := by linarith
  have h4 : |Real.cos ((k : ℝ) * Real.pi)| ^ 2 = 1 := by rw [sq_abs]; exact this
  exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).mp h4

lemma coef_norm_le (σ M : ℝ) (hσ : 0 < σ) (f : ℂ → ℂ) (hM : ∀ x : ℝ, ‖f (x : ℂ)‖ ≤ M) (k : ℤ) :
    ‖coef σ f k‖ ≤ M * σ / Real.pi ^ 2 * (1 / (((k : ℝ) + 1 / 2) ^ 2)) := by
  set t : ℝ := ((k : ℝ) + 1 / 2) * (Real.pi / σ) with ht
  have hnode : node σ k = ((t : ℝ) : ℂ) := by
    rw [ht]; unfold node; push_cast; ring
  have hk : ((k : ℝ) + 1 / 2) ≠ 0 := by
    intro h
    have : (2 * k + 1 : ℝ) = 0 := by linarith
    have : (2 * k + 1 : ℤ) = 0 := by exact_mod_cast this
    omega
  have hpi := Real.pi_pos
  have ht0 : t ≠ 0 := by
    rw [ht]; exact mul_ne_zero hk (by positivity)
  have hden : 0 < t ^ 2 * σ := by positivity
  have h1 : ‖coef σ f k‖ = ‖f (t : ℂ)‖ / (t ^ 2 * σ) := by
    unfold coef
    rw [norm_div, norm_mul, norm_pow, norm_mul, norm_neg, norm_sin_node σ hσ, hnode, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, sq_abs]
    rw [abs_of_pos hσ]
  rw [h1]
  have h2 : ‖f (t : ℂ)‖ / (t ^ 2 * σ) ≤ M / (t ^ 2 * σ) :=
    div_le_div_of_nonneg_right (hM t) hden.le
  refine h2.trans (le_of_eq ?_)
  rw [ht]
  field_simp

lemma summable_coef (σ M : ℝ) (hσ : 0 < σ) (f : ℂ → ℂ) (hM : ∀ x : ℝ, ‖f (x : ℂ)‖ ≤ M) :
    Summable (fun k : ℤ => coef σ f k) := by
  have h := hasSum_half_sq.mul_left (M * σ / Real.pi ^ 2)
  exact Summable.of_norm_bounded h.summable (coef_norm_le σ M hσ f hM)

lemma norm_tsum_coef_le (σ M : ℝ) (hσ : 0 < σ) (f : ℂ → ℂ) (hM : ∀ x : ℝ, ‖f (x : ℂ)‖ ≤ M) :
    ‖∑' k : ℤ, coef σ f k‖ ≤ σ * M := by
  have h := hasSum_half_sq.mul_left (M * σ / Real.pi ^ 2)
  have := tsum_of_norm_bounded h (coef_norm_le σ M hσ f hM)
  have hpi := Real.pi_pos
  refine this.trans (le_of_eq ?_)
  field_simp

lemma circle_small (σ M : ℝ) (hσ : 0 < σ) (f : ℂ → ℂ)
    (hb : ∀ z : ℂ, ‖f z‖ ≤ M * Real.exp (σ * |z.im|)) (m : ℕ) (hm : 1 ≤ m) :
    ‖∮ z in C(0, (m : ℝ) * Real.pi / σ), f z / (z ^ 2 * Complex.cos ((σ : ℂ) * z))‖ ≤
      8 * M * σ / m := by
  have hpi := Real.pi_pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set R : ℝ := (m : ℝ) * Real.pi / σ with hR
  have hR0 : 0 < R := by positivity
  have hM0 : 0 ≤ M := by
    have := hb 0
    simp at this
    exact (norm_nonneg _).trans this
  have hsph : ∀ z ∈ Metric.sphere (0 : ℂ) R,
      ‖f z / (z ^ 2 * Complex.cos ((σ : ℂ) * z))‖ ≤ 4 * M / R ^ 2 := by
    intro z hz
    have hzn : ‖z‖ = R := by simpa using hz
    have hw : ‖(σ : ℂ) * z‖ = m * Real.pi := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ, hzn, hR]
      field_simp
    have hcos := BernCos.cos_lower m hm _ hw
    have him : ((σ : ℂ) * z).im = σ * z.im := by simp
    rw [him, abs_mul, abs_of_pos hσ] at hcos
    have hE := Real.exp_pos (σ * |z.im|)
    rw [norm_div, norm_mul, norm_pow, hzn]
    have hden : 0 < R ^ 2 * ‖Complex.cos ((σ : ℂ) * z)‖ := by
      have : 0 < ‖Complex.cos ((σ : ℂ) * z)‖ := lt_of_lt_of_le (by positivity) hcos
      positivity
    rw [div_le_div_iff₀ hden (by positivity)]
    have h1 := hb z
    calc ‖f z‖ * R ^ 2 ≤ M * Real.exp (σ * |z.im|) * R ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 4 * M * (R ^ 2 * (Real.exp (σ * |z.im|) / 4)) := by ring
      _ ≤ 4 * M * (R ^ 2 * ‖Complex.cos ((σ : ℂ) * z)‖) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hcos (by positivity)
  have := circleIntegral.norm_integral_le_of_norm_le_const hR0.le hsph
  refine this.trans (le_of_eq ?_)
  rw [hR]
  field_simp
  ring

theorem riesz_bound (σ M : ℝ) (hσ : 0 < σ) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hb : ∀ z : ℂ, ‖f z‖ ≤ M * Real.exp (σ * |z.im|)) : ‖deriv f 0‖ ≤ σ * M := by
  have hM : ∀ x : ℝ, ‖f (x : ℂ)‖ ≤ M := by
    intro x; simpa using hb x
  have hpi := Real.pi_pos
  have hsum := (summable_coef σ M hσ f hM).hasSum
  -- partial sums over symmetric blocks converge to the full sum
  have hexh : Filter.Tendsto (fun m : ℕ => Finset.Ico (-(m : ℤ)) (m : ℤ)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_finset_of_monotone ?_ ?_
    · intro a b hab
      intro x hx
      simp only [Finset.mem_Ico] at hx ⊢
      have : (a : ℤ) ≤ b := by exact_mod_cast hab
      omega
    · intro x
      refine ⟨x.natAbs + 1, ?_⟩
      simp only [Finset.mem_Ico]
      omega
  have hlim : Filter.Tendsto (fun m : ℕ => ∑ k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), coef σ f k)
      Filter.atTop (nhds (∑' k : ℤ, coef σ f k)) := hsum.comp hexh
  have hlim2 : Filter.Tendsto (fun m : ℕ => deriv f 0 + ∑ k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), coef σ f k)
      Filter.atTop (nhds (deriv f 0 + ∑' k : ℤ, coef σ f k)) := hlim.const_add _
  have hsmall : ∀ m : ℕ, 1 ≤ m →
      ‖deriv f 0 + ∑ k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), coef σ f k‖ ≤ 4 * M * σ / (Real.pi * m) := by
    intro m hm
    have h1 := circle_small σ M hσ f hb m hm
    rw [BernB1.circle_residue σ hσ f hf m hm, norm_mul] at h1
    have h2 : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
      rw [norm_mul, norm_mul]; simp [abs_of_pos hpi]
    rw [h2] at h1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ hm0] at h1
    nlinarith [norm_nonneg (deriv f 0 + ∑ k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), coef σ f k)]
  have hzero : Filter.Tendsto (fun m : ℕ => 4 * M * σ / (Real.pi * m)) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun m : ℕ => (4 * M * σ / Real.pi) * (1 / (m : ℝ))) Filter.atTop (nhds 0) := by
      simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (4 * M * σ / Real.pi)
    refine this.congr (fun m => ?_)
    field_simp
  have hnorm : Filter.Tendsto (fun m : ℕ =>
      ‖deriv f 0 + ∑ k ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), coef σ f k‖) Filter.atTop
      (nhds ‖deriv f 0 + ∑' k : ℤ, coef σ f k‖) := hlim2.norm
  have hle : ‖deriv f 0 + ∑' k : ℤ, coef σ f k‖ ≤ 0 :=
    le_of_tendsto_of_tendsto hnorm hzero
      (Filter.eventually_atTop.mpr ⟨1, fun m hm => hsmall m hm⟩)
  have hz : deriv f 0 + ∑' k : ℤ, coef σ f k = 0 := norm_le_zero_iff.mp hle
  have : deriv f 0 = -∑' k : ℤ, coef σ f k := by linear_combination hz
  rw [this, norm_neg]
  exact norm_tsum_coef_le σ M hσ f hM

end SpectralSharpness.Dev.BernRiesz
end

section
set_option autoImplicit false

namespace SpectralSharpness.Dev.BernMain
open SpectralSharpness.NormalWindow SpectralSharpness.Dev

theorem bern_pos (σ M : ℝ) (hσ : 0 < σ) (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hexp : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp ((σ + ε) * ‖z‖))
    (hM : ∀ x : ℝ, ‖g (x : ℂ)‖ ≤ M) (x : ℝ) : ‖deriv g (x : ℂ)‖ ≤ σ * M := by
  set f : ℂ → ℂ := fun z => g (z + x) with hfdef
  have hf : Differentiable ℂ f := hg.comp (differentiable_id.add_const _)
  have hfexp : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp ((σ + ε) * ‖z‖) := by
    intro ε hε
    obtain ⟨C, hC⟩ := hexp ε hε
    have hC0 : 0 ≤ C := by
      have := hC 0
      simp at this
      exact (norm_nonneg _).trans this
    refine ⟨C * Real.exp ((σ + ε) * |x|), fun z => ?_⟩
    have h1 := hC (z + x)
    have h2 : ‖z + (x : ℂ)‖ ≤ ‖z‖ + |x| := by
      refine (norm_add_le _ _).trans ?_
      simp
    have h3 : Real.exp ((σ + ε) * ‖z + (x : ℂ)‖) ≤ Real.exp ((σ + ε) * |x|) * Real.exp ((σ + ε) * ‖z‖) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    calc ‖f z‖ ≤ C * Real.exp ((σ + ε) * ‖z + (x : ℂ)‖) := h1
      _ ≤ C * (Real.exp ((σ + ε) * |x|) * Real.exp ((σ + ε) * ‖z‖)) :=
          mul_le_mul_of_nonneg_left h3 hC0
      _ = _ := by ring
  have hfM : ∀ y : ℝ, ‖f (y : ℂ)‖ ≤ M := by
    intro y
    have := hM (y + x)
    simpa [hfdef] using this
  have hgrow := BernA.growth_bound σ M hσ f hf hfexp hfM
  have := BernRiesz.riesz_bound σ M hσ f hf hgrow
  have hd : deriv f 0 = deriv g (x : ℂ) := by
    have : deriv (fun z => g (z + (x : ℂ))) 0 = deriv g (0 + x) := by simpa using deriv_comp_add_const (f := g) (a := (x : ℂ)) (x := 0)
    simpa [hfdef] using this
  rwa [hd] at this

end SpectralSharpness.Dev.BernMain

namespace SpectralSharpness.NormalWindow
open SpectralSharpness.Dev.BernMain in
theorem chk_bernstein_exponential_type (τ M : ℝ) (hτ : 0 ≤ τ) (g : ℂ → ℂ)
    (hg : IsEntireOfExponentialTypeLE τ g) (hM : ∀ x : ℝ, ‖g (x : ℂ)‖ ≤ M) :
    ∀ x : ℝ, ‖deriv g (x : ℂ)‖ ≤ τ * M := by
  intro x
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  set δ : ℝ := ε / (M + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hexp : ∀ e : ℝ, 0 < e → ∃ C : ℝ, ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp (((τ + δ) + e) * ‖z‖) := by
    intro e he
    obtain ⟨C, hC⟩ := hg.2 (δ + e) (by linarith)
    exact ⟨C, fun z => by
      have := hC z
      rwa [show τ + (δ + e) = (τ + δ) + e by ring] at this⟩
  have := bern_pos (τ + δ) M (by linarith) g hg.1 hexp hM x
  have h2 : δ * M ≤ ε := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

end SpectralSharpness.NormalWindow
end

theorem solution : type_of% @SpectralSharpness.NormalWindow.chk_bernstein_exponential_type := @SpectralSharpness.NormalWindow.chk_bernstein_exponential_type
