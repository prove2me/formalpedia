-- Prove2me | solution 1 for StochLinOpt.UpperBound.freedman
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:00:31.942399+00:00
-- url     : https://prove2.me/submissions/34d450b7-57ec-4923-81fa-627230f83e2a

import Mathlib

open MeasureTheory

namespace StochLinOpt.UpperBound

lemma aux_fr_H (x : ℝ) : 0 ≤ (x - 1) * Real.exp x + 1 := by
  have h := Real.add_one_le_exp (-x)
  have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have hp := Real.exp_pos x
  nlinarith

lemma aux_fr_G_deriv (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y - 2) * Real.exp y + y + 2) ((x - 1) * Real.exp x + 1) x := by
  have h1 : HasDerivAt (fun y : ℝ => y - 2) 1 x := (hasDerivAt_id x).sub_const 2
  have h2 := (h1.mul (Real.hasDerivAt_exp x)).add (hasDerivAt_id x)
  have h3 := h2.add_const 2
  exact h3.congr_deriv (by ring)

lemma aux_fr_G_mono : Monotone (fun y : ℝ => (y - 2) * Real.exp y + y + 2) := by
  apply monotone_of_deriv_nonneg
  · intro x; exact (aux_fr_G_deriv x).differentiableAt
  · intro x; rw [(aux_fr_G_deriv x).deriv]; exact aux_fr_H x

lemma aux_fr_F_deriv (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2 / 2 - (1 - y / 3) * (Real.exp y - 1 - y))
      (((x - 2) * Real.exp x + x + 2) / 3) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
    simpa using (hasDerivAt_pow 2 x).div_const 2
  have h2 : HasDerivAt (fun y : ℝ => 1 - y / 3) (-(1/3)) x := by
    simpa using ((hasDerivAt_id x).div_const 3).const_sub 1
  have h3 : HasDerivAt (fun y : ℝ => Real.exp y - 1 - y) (Real.exp x - 1) x :=
    ((Real.hasDerivAt_exp x).sub_const 1).sub (hasDerivAt_id x)
  have := h1.sub (h2.mul h3)
  exact this.congr_deriv (by ring)

lemma aux_fr_exp_ineq (y : ℝ) : (1 - y / 3) * (Real.exp y - 1 - y) ≤ y ^ 2 / 2 := by
  set F : ℝ → ℝ := fun y => y ^ 2 / 2 - (1 - y / 3) * (Real.exp y - 1 - y) with hF
  have hG0 : ((0:ℝ) - 2) * Real.exp 0 + 0 + 2 = 0 := by simp
  have hcont : Continuous F := by
    rw [hF]; fun_prop
  have hdiff : Differentiable ℝ F := fun x => (aux_fr_F_deriv x).differentiableAt
  have hF0 : F 0 = 0 := by simp [hF]
  suffices 0 ≤ F y by simp only [hF] at this; linarith
  rcases le_total y 0 with hy | hy
  · have hanti : AntitoneOn F (Set.Iic 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Iic 0) hcont.continuousOn hdiff.differentiableOn
      intro x hx
      rw [interior_Iic] at hx
      rw [(aux_fr_F_deriv x).deriv]
      have := aux_fr_G_mono (le_of_lt (Set.mem_Iio.mp hx))
      simp only at this
      linarith
    have := hanti (Set.mem_Iic.mpr hy) (Set.mem_Iic.mpr le_rfl) hy
    linarith
  · have hmono : MonotoneOn F (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont.continuousOn hdiff.differentiableOn
      intro x hx
      rw [interior_Ici] at hx
      rw [(aux_fr_F_deriv x).deriv]
      have := aux_fr_G_mono (le_of_lt (Set.mem_Ioi.mp hx))
      simp only at this
      linarith
    have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
    linarith

lemma aux_fr_pw (l b x : ℝ) (hl : 0 < l) (hd : 0 < 1 - l * b / 3) (hx : x ≤ b) :
    Real.exp (l * x) ≤ 1 + l * x + l ^ 2 / (2 * (1 - l * b / 3)) * x ^ 2 := by
  have h1 := aux_fr_exp_ineq (l * x)
  have h2 : 0 ≤ Real.exp (l * x) - 1 - l * x := by
    have := Real.add_one_le_exp (l * x); linarith
  have h3 : l * x ≤ l * b := mul_le_mul_of_nonneg_left hx hl.le
  have h4 : (1 - l * b / 3) * (Real.exp (l * x) - 1 - l * x) ≤ (l * x) ^ 2 / 2 := by
    calc (1 - l * b / 3) * (Real.exp (l * x) - 1 - l * x)
        ≤ (1 - l * x / 3) * (Real.exp (l * x) - 1 - l * x) := by
          apply mul_le_mul_of_nonneg_right _ h2; linarith
      _ ≤ _ := h1
  have h5 : Real.exp (l * x) - 1 - l * x ≤ l ^ 2 / (2 * (1 - l * b / 3)) * x ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  linarith


lemma aux_fr_int_condExp {Ω : Type*} {m mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (hm : m ≤ mΩ) (Y Z : Ω → ℝ) (hY : StronglyMeasurable[m] Y)
    (hYZ : Integrable (fun ω => Y ω * Z ω) P) (hZ : Integrable Z P) :
    ∫ ω, Y ω * Z ω ∂P = ∫ ω, Y ω * (P[Z | m]) ω ∂P := by
  calc ∫ ω, Y ω * Z ω ∂P = ∫ ω, (P[Y * Z | m]) ω ∂P := (integral_condExp hm).symm
    _ = ∫ ω, (Y * P[Z | m]) ω ∂P :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hY hYZ hZ)
    _ = _ := rfl

lemma aux_fr_main {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (T : ℕ) (b : ℝ)
    (hmeas : ∀ i ∈ Finset.Icc 1 T, Measurable[𝓕 (i + 1)] (X i))
    (hint : ∀ i ∈ Finset.Icc 1 T, Integrable (X i) P)
    (hint_sq : ∀ i ∈ Finset.Icc 1 T, Integrable (fun ω => X i ω ^ 2) P)
    (hmds : ∀ i ∈ Finset.Icc 1 T, P[X i | 𝓕 i] =ᵐ[P] 0)
    (hb : ∀ i ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, X i ω ≤ b)
    (l c : ℝ) (hl : 0 < l) (hc : 0 ≤ c)
    (hpw : ∀ x ≤ b, Real.exp (l * x) ≤ 1 + l * x + c * x ^ 2)
    (V : ℕ → Ω → ℝ) (hV : ∀ i, V i = P[fun ω' => X i ω' ^ 2 | 𝓕 i]) :
    ∀ k ≤ T, Integrable (fun ω => Real.exp (l * ∑ i ∈ Finset.Icc 1 k, X i ω
        - c * ∑ i ∈ Finset.Icc 1 k, V i ω)) P ∧
      ∫ ω, Real.exp (l * ∑ i ∈ Finset.Icc 1 k, X i ω
        - c * ∑ i ∈ Finset.Icc 1 k, V i ω) ∂P ≤ 1 := by
  have hVsm : ∀ i, StronglyMeasurable[𝓕 i] (V i) := fun i => by
    rw [hV]; exact stronglyMeasurable_condExp
  have hVint : ∀ i, Integrable (V i) P := fun i => by rw [hV]; exact integrable_condExp
  have hVnn : ∀ i, 0 ≤ᵐ[P] V i := fun i => by
    rw [hV]; exact condExp_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
  have hgood : ∀ᵐ ω ∂P, ∀ i ∈ Finset.Icc 1 T, X i ω ≤ b ∧ 0 ≤ V i ω := by
    rw [Filter.eventually_all_finset]
    intro i hi
    filter_upwards [hb i hi, hVnn i] with ω h1 h2
    exact ⟨h1, h2⟩
  have hXm0 : ∀ i ∈ Finset.Icc 1 T, Measurable (X i) := fun i hi =>
    (hmeas i hi).mono (𝓕.le _) le_rfl
  have hWm : ∀ k, Measurable[𝓕 k] (fun ω => ∑ i ∈ Finset.Icc 1 k, V i ω) := fun k =>
    Finset.measurable_sum _ (fun i hi =>
      (hVsm i).measurable.mono (𝓕.mono (by simp at hi; omega)) le_rfl)
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    obtain ⟨ihint, ihle⟩ := ih (by omega)
    have hk1 : k + 1 ∈ Finset.Icc 1 T := Finset.mem_Icc.mpr ⟨by omega, hk⟩
    have hSm : Measurable[𝓕 (k+1)] (fun ω => ∑ i ∈ Finset.Icc 1 k, X i ω) :=
      Finset.measurable_sum _ (fun i hi =>
        (hmeas i (by simp at hi ⊢; omega)).mono (𝓕.mono (by simp at hi; omega)) le_rfl)
    set Y : Ω → ℝ := fun ω => Real.exp (l * ∑ i ∈ Finset.Icc 1 k, X i ω
        - c * ∑ i ∈ Finset.Icc 1 k, V i ω - c * V (k+1) ω) with hYdef
    have hYm : StronglyMeasurable[𝓕 (k+1)] Y := by
      have : Measurable[𝓕 (k+1)] Y := by
        apply Real.measurable_exp.comp
        exact ((hSm.const_mul l).sub (((hWm k).mono (𝓕.mono (Nat.le_succ k)) le_rfl).const_mul c)).sub
          ((hVsm (k+1)).measurable.const_mul c)
      exact this.stronglyMeasurable
    have hYae : AEStronglyMeasurable Y P := (hYm.mono (𝓕.le _)).aestronglyMeasurable
    have hYbd : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ Real.exp (l * ∑ i ∈ Finset.Icc 1 k, b) := by
      filter_upwards [hgood] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have h1 : ∑ i ∈ Finset.Icc 1 k, X i ω ≤ ∑ i ∈ Finset.Icc 1 k, b :=
        Finset.sum_le_sum (fun i hi => (hω i (by simp at hi ⊢; omega)).1)
      have h2 : 0 ≤ ∑ i ∈ Finset.Icc 1 k, V i ω :=
        Finset.sum_nonneg (fun i hi => (hω i (by simp at hi ⊢; omega)).2)
      have h3 : 0 ≤ V (k+1) ω := (hω (k+1) hk1).2
      nlinarith [mul_le_mul_of_nonneg_left h1 hl.le, mul_nonneg hc h2, mul_nonneg hc h3]
    have hYint : Integrable Y P := Integrable.of_bound hYae _ hYbd
    have hEm : Measurable (fun ω => Real.exp (l * X (k+1) ω)) :=
      Real.measurable_exp.comp ((hXm0 _ hk1).const_mul l)
    have hEint : Integrable (fun ω => Real.exp (l * X (k+1) ω)) P := by
      refine Integrable.of_bound hEm.aestronglyMeasurable (Real.exp (l * b)) ?_
      filter_upwards [hgood] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hω (k+1) hk1).1 hl.le)
    have hfun : (fun ω => Real.exp (l * ∑ i ∈ Finset.Icc 1 (k+1), X i ω
        - c * ∑ i ∈ Finset.Icc 1 (k+1), V i ω)) =
        fun ω => Y ω * Real.exp (l * X (k+1) ω) := by
      funext ω
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), hYdef,
        ← Real.exp_add]
      congr 1; ring
    have hMint : Integrable (fun ω => Y ω * Real.exp (l * X (k+1) ω)) P :=
      hEint.bdd_mul hYae hYbd
    rw [hfun]
    refine ⟨hMint, ?_⟩
    have hYX : Integrable (fun ω => Y ω * X (k+1) ω) P := (hint _ hk1).bdd_mul hYae hYbd
    have hYX2 : Integrable (fun ω => Y ω * X (k+1) ω ^ 2) P := (hint_sq _ hk1).bdd_mul hYae hYbd
    have hYV : Integrable (fun ω => Y ω * V (k+1) ω) P := (hVint _).bdd_mul hYae hYbd
    have hYX0 : ∫ ω, Y ω * X (k+1) ω ∂P = 0 := by
      rw [aux_fr_int_condExp P (𝓕.le (k+1)) Y (X (k+1)) hYm hYX (hint _ hk1)]
      rw [integral_congr_ae (g := fun _ => (0:ℝ)) ?_]
      · simp
      filter_upwards [hmds _ hk1] with ω hω
      simp [hω]
    have hYX2V : ∫ ω, Y ω * X (k+1) ω ^ 2 ∂P = ∫ ω, Y ω * V (k+1) ω ∂P := by
      rw [aux_fr_int_condExp P (𝓕.le (k+1)) Y (fun ω => X (k+1) ω ^ 2) hYm hYX2 (hint_sq _ hk1),
        hV]
    have hYpos : ∀ ω, 0 < Y ω := fun ω => Real.exp_pos _
    have i1 : Integrable (fun ω => Y ω + l * (Y ω * X (k+1) ω)) P := hYint.add (hYX.const_mul l)
    have i2 : Integrable (fun ω => Y ω + l * (Y ω * X (k+1) ω) + c * (Y ω * X (k+1) ω ^ 2)) P :=
      i1.add (hYX2.const_mul c)
    have i3 : Integrable (fun ω => Y ω + c * (Y ω * V (k+1) ω)) P := hYint.add (hYV.const_mul c)
    calc ∫ ω, Y ω * Real.exp (l * X (k+1) ω) ∂P
        ≤ ∫ ω, (Y ω + l * (Y ω * X (k+1) ω) + c * (Y ω * X (k+1) ω ^ 2)) ∂P := by
          apply integral_mono_ae hMint i2
          filter_upwards [hgood] with ω hω
          have := mul_le_mul_of_nonneg_left (hpw _ (hω (k+1) hk1).1) (hYpos ω).le
          linarith
      _ = ∫ ω, Y ω ∂P + l * ∫ ω, Y ω * X (k+1) ω ∂P + c * ∫ ω, Y ω * X (k+1) ω ^ 2 ∂P := by
          have e1 : ∫ ω, (Y ω + l * (Y ω * X (k+1) ω) + c * (Y ω * X (k+1) ω ^ 2)) ∂P =
              ∫ ω, (Y ω + l * (Y ω * X (k+1) ω)) ∂P + ∫ ω, c * (Y ω * X (k+1) ω ^ 2) ∂P :=
            integral_add i1 (hYX2.const_mul c)
          have e2 : ∫ ω, (Y ω + l * (Y ω * X (k+1) ω)) ∂P =
              ∫ ω, Y ω ∂P + ∫ ω, l * (Y ω * X (k+1) ω) ∂P :=
            integral_add hYint (hYX.const_mul l)
          rw [e1, e2, integral_const_mul, integral_const_mul]
      _ = ∫ ω, (Y ω + c * (Y ω * V (k+1) ω)) ∂P := by
          have e3 : ∫ ω, (Y ω + c * (Y ω * V (k+1) ω)) ∂P =
              ∫ ω, Y ω ∂P + ∫ ω, c * (Y ω * V (k+1) ω) ∂P :=
            integral_add hYint (hYV.const_mul c)
          rw [hYX0, hYX2V, e3, integral_const_mul]; ring
      _ ≤ ∫ ω, Real.exp (l * ∑ i ∈ Finset.Icc 1 k, X i ω
            - c * ∑ i ∈ Finset.Icc 1 k, V i ω) ∂P := by
          apply integral_mono_ae i3 ihint
          filter_upwards with ω
          show Y ω + c * (Y ω * V (k+1) ω) ≤ _
          have hY : Y ω = Real.exp (l * ∑ i ∈ Finset.Icc 1 k, X i ω
              - c * ∑ i ∈ Finset.Icc 1 k, V i ω - c * V (k+1) ω) := rfl
          have h1 := Real.add_one_le_exp (c * V (k+1) ω)
          have h2 : Y ω * Real.exp (c * V (k+1) ω) = Real.exp (l * ∑ i ∈ Finset.Icc 1 k, X i ω
              - c * ∑ i ∈ Finset.Icc 1 k, V i ω) := by
            rw [hY, ← Real.exp_add]; congr 1; ring
          have h3 := hYpos ω
          nlinarith
      _ ≤ 1 := ihle

theorem aux_fr_final {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (T : ℕ) (b : ℝ)
    (hmeas : ∀ i ∈ Finset.Icc 1 T, Measurable[𝓕 (i + 1)] (X i))
    (hint : ∀ i ∈ Finset.Icc 1 T, Integrable (X i) P)
    (hint_sq : ∀ i ∈ Finset.Icc 1 T, Integrable (fun ω => X i ω ^ 2) P)
    (hmds : ∀ i ∈ Finset.Icc 1 T, P[X i | 𝓕 i] =ᵐ[P] 0)
    (hb : ∀ i ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, X i ω ≤ b)
    (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    P.real {ω | a ≤ ∑ i ∈ Finset.Icc 1 T, X i ω ∧
        ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | 𝓕 i] ω ≤ v} ≤
      Real.exp (-a ^ 2 / (2 * v + 2 * a * b / 3)) := by
  by_cases hD : 2 * v + 2 * a * b / 3 ≤ 0
  · have h1 : 1 ≤ Real.exp (-a ^ 2 / (2 * v + 2 * a * b / 3)) := by
      apply Real.one_le_exp
      exact div_nonneg_of_nonpos (by nlinarith) hD
    exact le_trans measureReal_le_one h1
  push Not at hD
  have hD' : 0 < v + a * b / 3 := by linarith
  set l := a / (v + a * b / 3) with hl_def
  have hl : 0 < l := div_pos ha hD'
  have hne' : v * 3 + a * b ≠ 0 := by
    have : 0 < v * 3 + a * b := by linarith
    exact this.ne'
  have hd : 1 - l * b / 3 = v / (v + a * b / 3) := by
    have hne : v + a * b / 3 ≠ 0 := hD'.ne'
    rw [hl_def]
    field_simp
    ring
  have hdpos : 0 < 1 - l * b / 3 := by rw [hd]; exact div_pos hv hD'
  set c := l ^ 2 / (2 * (1 - l * b / 3)) with hc_def
  have hc : 0 ≤ c := by positivity
  have hpw : ∀ x ≤ b, Real.exp (l * x) ≤ 1 + l * x + c * x ^ 2 := fun x hx =>
    aux_fr_pw l b x hl hdpos hx
  obtain ⟨hMint, hMle⟩ := aux_fr_main P 𝓕 X T b hmeas hint hint_sq hmds hb l c hl hc hpw
    (fun i => P[fun ω' => X i ω' ^ 2 | 𝓕 i]) (fun i => rfl) T le_rfl
  set ε := Real.exp (l * a - c * v) with hε
  have hεpos : 0 < ε := Real.exp_pos _
  have hsub : {ω | a ≤ ∑ i ∈ Finset.Icc 1 T, X i ω ∧
        ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | 𝓕 i] ω ≤ v} ⊆
      {ω | ε ≤ Real.exp (l * ∑ i ∈ Finset.Icc 1 T, X i ω
        - c * ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | 𝓕 i] ω)} := by
    intro ω hω
    obtain ⟨h1, h2⟩ := hω
    simp only [Set.mem_ofPred_eq, hε]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left h1 hl.le, mul_le_mul_of_nonneg_left h2 hc]
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le)) hMint ε
  have hmono := measureReal_mono (μ := P) hsub
  have key : P.real {ω | ε ≤ Real.exp (l * ∑ i ∈ Finset.Icc 1 T, X i ω
        - c * ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | 𝓕 i] ω)} ≤ ε⁻¹ := by
    have h1 := hmk.trans hMle
    calc _ = ε⁻¹ * (ε * P.real {ω | ε ≤ Real.exp (l * ∑ i ∈ Finset.Icc 1 T, X i ω
        - c * ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | 𝓕 i] ω)}) := by
          rw [← mul_assoc, inv_mul_cancel₀ hεpos.ne', one_mul]
      _ ≤ ε⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hεpos.le)
      _ = ε⁻¹ := mul_one _
  have halg : ε⁻¹ = Real.exp (-a ^ 2 / (2 * v + 2 * a * b / 3)) := by
    rw [hε, ← Real.exp_neg]
    congr 1
    rw [hc_def, hd, hl_def]
    field_simp
    ring
  linarith

end StochLinOpt.UpperBound

open MeasureTheory StochLinOpt.UpperBound

theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (T : ℕ) (b : ℝ)
    (hmeas : ∀ i ∈ Finset.Icc 1 T, Measurable[𝓕 (i + 1)] (X i))
    (hint : ∀ i ∈ Finset.Icc 1 T, Integrable (X i) P)
    (hint_sq : ∀ i ∈ Finset.Icc 1 T, Integrable (fun ω => X i ω ^ 2) P)
    (hmds : ∀ i ∈ Finset.Icc 1 T, P[X i | 𝓕 i] =ᵐ[P] 0)
    (hb : ∀ i ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, X i ω ≤ b)
    (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    P.real {ω | a ≤ ∑ i ∈ Finset.Icc 1 T, X i ω ∧
        ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | 𝓕 i] ω ≤ v} ≤
      Real.exp (-a ^ 2 / (2 * v + 2 * a * b / 3)) :=
  aux_fr_final P 𝓕 X T b hmeas hint hint_sq hmds hb a v ha hv
