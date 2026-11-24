-- Prove2me | solution 1 for RoughSurfaceScattering.weak_deriv_removable_point
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T16:20:27.667826+00:00
-- url     : https://prove2.me/submissions/28f7548e-e530-48b6-9b2e-b70bf31ed5eb

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory Metric Filter Topology
open RoughSurfaceScattering

/-- The cut-off `ζ(w) = 1 - S((|w|² - 1)/3)`: `1` on `B̄(0,1)`, `0` outside `B(0,2)`. -/
noncomputable def zeta (w : R2) : ℝ := 1 - Real.smoothTransition ((‖w‖ ^ 2 - 1) / 3)

lemma zeta_contDiff {n : ℕ∞} : ContDiff ℝ n zeta :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp
    (((contDiff_norm_sq ℝ).sub contDiff_const).div_const _))

lemma zeta_nonneg (w : R2) : 0 ≤ zeta w := by
  unfold zeta; linarith [Real.smoothTransition.le_one ((‖w‖ ^ 2 - 1) / 3)]

lemma zeta_le_one (w : R2) : zeta w ≤ 1 := by
  unfold zeta; linarith [Real.smoothTransition.nonneg ((‖w‖ ^ 2 - 1) / 3)]

lemma zeta_eq_zero (w : R2) (hw : 2 ≤ ‖w‖) : zeta w = 0 := by
  unfold zeta
  rw [Real.smoothTransition.one_of_one_le]; · ring
  have : 4 ≤ ‖w‖ ^ 2 := by nlinarith
  rw [le_div_iff₀ (by norm_num)]; linarith

lemma zeta_eq_one (w : R2) (hw : ‖w‖ ≤ 1) : zeta w = 1 := by
  unfold zeta
  rw [Real.smoothTransition.zero_of_nonpos]; · ring
  have : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith

lemma zeta_hasCompactSupport : HasCompactSupport zeta :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 2) fun w hw => by
    by_contra h
    rw [mem_closedBall, dist_zero_right, not_le] at h
    exact hw (zeta_eq_zero w h.le)

/-- `ζ_ε(x) = ζ((x - y)/ε)`. -/
noncomputable def zetaE (y : R2) (ε : ℝ) (x : R2) : ℝ := zeta (ε⁻¹ • (x - y))

lemma zetaE_contDiff (y : R2) (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (zetaE y ε) :=
  zeta_contDiff.comp ((contDiff_id.sub contDiff_const).const_smul _)

lemma fderiv_zetaE_norm (y : R2) (ε : ℝ) (hε : 0 < ε) (x : R2) :
    ‖fderiv ℝ (zetaE y ε) x‖ = ε⁻¹ * ‖fderiv ℝ zeta (ε⁻¹ • (x - y))‖ := by
  have hd : HasFDerivAt (zetaE y ε)
      ((fderiv ℝ zeta (ε⁻¹ • (x - y))).comp (ε⁻¹ • ContinuousLinearMap.id ℝ R2)) x := by
    have h1 : HasFDerivAt (fun x : R2 => ε⁻¹ • (x - y)) (ε⁻¹ • ContinuousLinearMap.id ℝ R2) x :=
      ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const y).const_smul ε⁻¹
    exact ((zeta_contDiff (n := 1)).differentiable one_ne_zero _).hasFDerivAt.comp x h1
  rw [hd.fderiv, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id, norm_smul,
    Real.norm_of_nonneg (by positivity)]

lemma integral_comp_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : R2 → E) (y : R2) (ε : ℝ) (hε : 0 < ε) :
    ∫ x, F (ε⁻¹ • (x - y)) = ε ^ 2 • ∫ w, F w := by
  rw [integral_sub_right_eq_self (fun x => F (ε⁻¹ • x)) y,
    Measure.integral_comp_smul volume F ε⁻¹, finrank_euclideanSpace_fin]
  congr 1
  rw [inv_pow, inv_inv, abs_of_pos (by positivity)]

lemma integral_zetaE (y : R2) (ε : ℝ) (hε : 0 < ε) :
    ∫ x, zetaE y ε x = ε ^ 2 * ∫ w, zeta w := by
  simpa [zetaE] using integral_comp_affine zeta y ε hε

lemma integral_fderiv_zetaE (y : R2) (ε : ℝ) (hε : 0 < ε) :
    ∫ x, ‖fderiv ℝ (zetaE y ε) x‖ = ε * ∫ w, ‖fderiv ℝ zeta w‖ := by
  simp only [fderiv_zetaE_norm y ε hε]
  rw [integral_const_mul, integral_comp_affine (fun w => ‖fderiv ℝ zeta w‖) y ε hε, smul_eq_mul]
  field_simp

lemma zetaE_eq_zero (y : R2) (ε : ℝ) (hε : 0 < ε) (x : R2) (hx : 2 * ε ≤ ‖x - y‖) :
    zetaE y ε x = 0 := by
  apply zeta_eq_zero
  rw [norm_smul, Real.norm_of_nonneg (by positivity), le_inv_mul_iff₀ hε]
  linarith

lemma zetaE_eq_one (y : R2) (ε : ℝ) (hε : 0 < ε) (x : R2) (hx : ‖x - y‖ ≤ ε) :
    zetaE y ε x = 1 := by
  apply zeta_eq_one
  rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_le_iff₀ hε]
  linarith

lemma integrable_of_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : R2 → E) (K : Set R2) (hK : IsCompact K) (hc : ContinuousOn F K)
    (h0 : ∀ x, x ∉ K → F x = 0) : Integrable F := by
  have hind : Set.indicator K F = F := by
    funext x; by_cases hx : x ∈ K <;> simp [hx, h0 x]
  rw [← hind, integrable_indicator_iff hK.measurableSet]
  exact hc.integrableOn_compact hK

lemma fderiv_ofReal_apply (φ : R2 → ℝ) (hφ : Differentiable ℝ φ) (x v : R2) :
    fderiv ℝ (fun x => (φ x : ℂ)) x v = ((fderiv ℝ φ x v : ℝ) : ℂ) := by
  have := (Complex.ofRealCLM.hasFDerivAt (x := φ x)).comp x (hφ x).hasFDerivAt
  rw [show (fun x => (φ x : ℂ)) = Complex.ofRealCLM ∘ φ from rfl, this.fderiv]
  simp

lemma zetaE_support (y : R2) (ε : ℝ) (hε : 0 < ε) :
    Function.support (zetaE y ε) ⊆ closedBall y (2 * ε) := by
  intro x hx
  by_contra h
  rw [mem_closedBall, dist_eq_norm, not_le] at h
  exact hx (zetaE_eq_zero y ε hε x h.le)

lemma tsupport_zetaE (y : R2) (ε : ℝ) (hε : 0 < ε) :
    tsupport (zetaE y ε) ⊆ closedBall y (2 * ε) :=
  closure_minimal (zetaE_support y ε hε) isClosed_closedBall

theorem solution (U : Set R2) (hU : IsOpen U) (y : R2) (g : R2 → ℂ)
    (hc : ContinuousOn g U) (hd : ∀ x ∈ U, x ≠ y → DifferentiableAt ℝ g x) (v : R2)
    (hint : IntegrableOn (fun x => fderiv ℝ g x v) U) :
    IsWeakDeriv U g v (fun x => fderiv ℝ g x v) := by
  intro φ hφ hcs hts
  set K := tsupport φ with hKdef
  have hK : IsCompact K := hcs
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφc : Continuous φ := hφd.continuous
  have hdφc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hφ0 : ∀ x, x ∉ K → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hdφ0 : ∀ x, x ∉ K → fderiv ℝ φ x = 0 := fun x hx =>
    Function.notMem_support.mp fun h => hx (support_fderiv_subset ℝ h)
  have hgK : ContinuousOn g K := hc.mono hts
  obtain ⟨Mg0, hMg0⟩ := hK.exists_bound_of_continuousOn hgK
  set Mg := max Mg0 0
  have hMg : ∀ x ∈ K, ‖g x‖ ≤ Mg := fun x hx => (hMg0 x hx).trans (le_max_left _ _)
  have hMgnn : 0 ≤ Mg := le_max_right _ _
  obtain ⟨Mφ, hMφ⟩ := hφc.bounded_above_of_compact_support hcs
  obtain ⟨Mdφ, hMdφ⟩ := hdφc.bounded_above_of_compact_support (hcs.fderiv (𝕜 := ℝ))
  have hdgK : IntegrableOn (fun x => fderiv ℝ g x v) K := hint.mono_set hts
  -- integrals over `U` are integrals over the plane
  have hout1 : ∀ x, x ∉ U → g x * ((fderiv ℝ φ x v : ℝ) : ℂ) = 0 := fun x hx => by
    rw [hdφ0 x fun h => hx (hts h)]; simp
  have hout2 : ∀ x, x ∉ U → fderiv ℝ g x v * (φ x : ℂ) = 0 := fun x hx => by
    rw [hφ0 x fun h => hx (hts h)]; simp
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout1,
    setIntegral_eq_integral_of_forall_compl_eq_zero hout2]
  -- integrability of `∂g · w` for `w` continuous and vanishing off `K`
  have hint_dg : ∀ w : R2 → ℝ, Continuous w → (∀ x, x ∉ K → w x = 0) →
      Integrable fun x => fderiv ℝ g x v * (w x : ℂ) := by
    intro w hw hw0
    refine (integrableOn_iff_integrable_of_support_subset fun x hx => ?_).mp
      (hdgK.mul_continuousOn (Complex.continuous_ofReal.comp hw).continuousOn hK)
    by_contra hxK; exact hx (by simp [hw0 x hxK])
  have hint_g : ∀ w : R2 → ℝ, Continuous w → (∀ x, x ∉ K → w x = 0) →
      Integrable fun x => g x * (w x : ℂ) := by
    intro w hw hw0
    exact integrable_of_compact _ K hK (hgK.mul (Complex.continuous_ofReal.comp hw).continuousOn)
      fun x hx => by simp [hw0 x hx]
  -- the cut-offs
  set εn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεn
  have hεpos : ∀ n, 0 < εn n := fun n => by positivity
  set Z : ℕ → R2 → ℝ := fun n => zetaE y (εn n) with hZ
  have hZd : ∀ n, Differentiable ℝ (Z n) := fun n =>
    (zetaE_contDiff y (εn n) (n := 1)).differentiable one_ne_zero
  have hZc : ∀ n, Continuous (Z n) := fun n => (hZd n).continuous
  have hdZc : ∀ n, Continuous (fderiv ℝ (Z n)) := fun n =>
    (zetaE_contDiff y (εn n) (n := 1)).continuous_fderiv one_ne_zero
  set ψ : ℕ → R2 → ℝ := fun n x => φ x * (1 - Z n x) with hψ
  have hψd : ∀ n, Differentiable ℝ (ψ n) := fun n => hφd.mul ((differentiable_const (1:ℝ)).sub (hZd n))
  have hψ0 : ∀ n x, x ∉ K → ψ n x = 0 := fun n x hx => by simp [hψ, hφ0 x hx]
  have hdψ : ∀ n x, fderiv ℝ (ψ n) x v =
      fderiv ℝ φ x v - (fderiv ℝ φ x v * Z n x + φ x * fderiv ℝ (Z n) x v) := by
    intro n x
    rw [show ψ n = φ * ((fun _ => (1:ℝ)) - Z n) from rfl,
      ((hφd x).hasFDerivAt.mul ((hasFDerivAt_const (1:ℝ) x).sub
      (hZd n x).hasFDerivAt)).fderiv]
    simp; ring
  have hytsupp : ∀ n, y ∉ tsupport (ψ n) := by
    intro n
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [ball_mem_nhds y (hεpos n)] with x hx
    rw [mem_ball, dist_eq_norm] at hx
    simp [hψ, hZ, zetaE_eq_one y (εn n) (hεpos n) x hx.le]
  have hdψ0 : ∀ n x, x ∉ K → fderiv ℝ (ψ n) x = 0 := by
    intro n x hx
    have : x ∉ tsupport (ψ n) := fun h => hx (closure_minimal (fun z hz => by
      by_contra hzK; exact hz (hψ0 n z hzK)) isClosed_closure |>.trans (le_of_eq rfl) h)
    exact Function.notMem_support.mp fun h => this (support_fderiv_subset ℝ h)
  -- integration by parts for each `n`
  have hibp : ∀ n, ∫ x, g x * ((fderiv ℝ (ψ n) x v : ℝ) : ℂ) =
      -∫ x, fderiv ℝ g x v * (ψ n x : ℂ) := by
    intro n
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := g) (g := fun x => (ψ n x : ℂ)) (v := v)
      (hint_dg _ ((hψd n).continuous) (hψ0 n))
      (by
        simp only [fderiv_ofReal_apply (ψ n) (hψd n)]
        refine integrable_of_compact _ K hK (hgK.mul ?_) fun x hx => by simp [hdψ0 n x hx]
        exact (Complex.continuous_ofReal.comp ((by
          simp only [hdψ]; fun_prop : Continuous fun x => fderiv ℝ (ψ n) x v))).continuousOn)
      (hint_g _ ((hψd n).continuous) (hψ0 n))
      (fun x hx => by
        have hx' : x ∈ tsupport (ψ n) :=
          tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero (ψ n) hx
        have hxK : x ∈ K := closure_minimal (fun z hz => by
          by_contra hzK; exact hz (hψ0 n z hzK)) isClosed_closure hx'
        exact hd x (hts hxK) fun h => hytsupp n (h ▸ hx'))
      (fun x _ => by
        simpa [Function.comp_def] using Complex.ofRealCLM.differentiableAt.comp x (hψd n x))
    simpa only [fderiv_ofReal_apply (ψ n) (hψd n)] using h
  -- the two error terms
  set A : ℕ → ℂ := fun n => ∫ x, g x *
      ((fderiv ℝ φ x v * Z n x + φ x * fderiv ℝ (Z n) x v : ℝ) : ℂ) with hA
  set B : ℕ → ℂ := fun n => ∫ x, fderiv ℝ g x v * ((φ x * Z n x : ℝ) : ℂ) with hB
  have hcA : ∀ n, Continuous fun x => fderiv ℝ φ x v * Z n x + φ x * fderiv ℝ (Z n) x v :=
    fun n => by fun_prop
  have hkey : ∀ n, (∫ x, g x * ((fderiv ℝ φ x v : ℝ) : ℂ)) + ∫ x, fderiv ℝ g x v * (φ x : ℂ) =
      A n + B n := by
    intro n
    have h := hibp n
    simp only [hdψ] at h
    have e1 : (fun x => g x * ((fderiv ℝ φ x v -
        (fderiv ℝ φ x v * Z n x + φ x * fderiv ℝ (Z n) x v) : ℝ) : ℂ)) =
        fun x => g x * ((fderiv ℝ φ x v : ℝ) : ℂ) -
          g x * ((fderiv ℝ φ x v * Z n x + φ x * fderiv ℝ (Z n) x v : ℝ) : ℂ) := by
      funext x; push_cast; ring
    have e2 : (fun x => fderiv ℝ g x v * ((ψ n x : ℝ) : ℂ)) =
        fun x => fderiv ℝ g x v * (φ x : ℂ) - fderiv ℝ g x v * ((φ x * Z n x : ℝ) : ℂ) := by
      funext x; simp only [hψ]; push_cast; ring
    rw [e1, e2, integral_sub, integral_sub] at h
    · simp only [hA, hB]
      have e : ∀ a b c d : ℂ, a - b = -(c - d) → a + c = b + d := by
        intro a b c d h; linear_combination h
      exact e _ _ _ _ h
    · exact hint_dg φ hφc hφ0
    · exact hint_dg _ (hφc.mul (hZc n)) fun x hx => by simp [hφ0 x hx]
    · exact hint_g _ (hdφc.clm_apply continuous_const) fun x hx => by simp [hdφ0 x hx]
    · exact hint_g _ (hcA n) fun x hx => by simp [hdφ0 x hx, hφ0 x hx]
  -- `A n → 0`
  set I1 := ∫ w, ‖fderiv ℝ zeta w‖
  set J := ∫ w, zeta w
  have hεlim : Tendsto εn atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hAlim : Tendsto A atTop (𝓝 0) := by
    have hbd : ∀ n, ‖A n‖ ≤ Mg * ‖v‖ * (Mdφ * (εn n ^ 2 * J) + Mφ * (εn n * I1)) := by
      intro n
      have hZint : Integrable (Z n) := integrable_of_compact _ _ (isCompact_closedBall y (2 * εn n))
        (hZc n).continuousOn fun x hx => Function.notMem_support.mp fun h =>
          hx (zetaE_support y (εn n) (hεpos n) h)
      have hdZint : Integrable fun x => ‖fderiv ℝ (Z n) x‖ :=
        integrable_of_compact _ _ (isCompact_closedBall y (2 * εn n)) (hdZc n).norm.continuousOn
          fun x hx => by
            rw [Function.notMem_support.mp fun h => hx (tsupport_zetaE y (εn n) (hεpos n)
              (support_fderiv_subset ℝ h)), norm_zero]
      calc ‖A n‖ ≤ ∫ x, Mg * ‖v‖ * (Mdφ * Z n x + Mφ * ‖fderiv ℝ (Z n) x‖) := by
            refine norm_integral_le_of_norm_le (by fun_prop) (Eventually.of_forall fun x => ?_)
            by_cases hx : x ∈ K
            · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
              have h1 : |fderiv ℝ φ x v * Z n x + φ x * fderiv ℝ (Z n) x v| ≤
                  ‖v‖ * (Mdφ * Z n x + Mφ * ‖fderiv ℝ (Z n) x‖) := by
                have ha : |fderiv ℝ φ x v| ≤ Mdφ * ‖v‖ := by
                  rw [← Real.norm_eq_abs]
                  exact (ContinuousLinearMap.le_opNorm _ _).trans
                    (mul_le_mul_of_nonneg_right (hMdφ x) (norm_nonneg _))
                have hb : |fderiv ℝ (Z n) x v| ≤ ‖fderiv ℝ (Z n) x‖ * ‖v‖ := by
                  rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
                have hφx : |φ x| ≤ Mφ := by rw [← Real.norm_eq_abs]; exact hMφ x
                have hZx : 0 ≤ Z n x := zeta_nonneg _
                calc _ ≤ |fderiv ℝ φ x v| * Z n x + |φ x| * |fderiv ℝ (Z n) x v| := by
                      refine (abs_add_le _ _).trans ?_
                      rw [abs_mul, abs_mul, abs_of_nonneg hZx]
                  _ ≤ (Mdφ * ‖v‖) * Z n x + Mφ * (‖fderiv ℝ (Z n) x‖ * ‖v‖) := by
                      gcongr
                      · exact (abs_nonneg _).trans hφx
                  _ = _ := by ring
              calc ‖g x‖ * |fderiv ℝ φ x v * Z n x + φ x * fderiv ℝ (Z n) x v| ≤ Mg * (‖v‖ * (Mdφ * Z n x + Mφ * ‖fderiv ℝ (Z n) x‖)) :=
                    mul_le_mul (hMg x hx) h1 (abs_nonneg _) ((norm_nonneg _).trans (hMg x hx))
                _ = _ := by ring
            · rw [hdφ0 x hx, hφ0 x hx]
              have hMφnn : 0 ≤ Mφ := (norm_nonneg _).trans (hMφ 0)
              have hMdφnn : 0 ≤ Mdφ := (norm_nonneg _).trans (hMdφ 0)
              have hZx : 0 ≤ Z n x := zeta_nonneg _
              simp
              positivity
        _ = Mg * ‖v‖ * (Mdφ * (εn n ^ 2 * J) + Mφ * (εn n * I1)) := by
            rw [integral_const_mul, integral_add (hZint.const_mul _) (hdZint.const_mul _),
              integral_const_mul, integral_const_mul, integral_zetaE y _ (hεpos n),
              integral_fderiv_zetaE y _ (hεpos n)]
    have hlim0 : Tendsto (fun n => Mg * ‖v‖ * (Mdφ * (εn n ^ 2 * J) + Mφ * (εn n * I1)))
        atTop (𝓝 0) := by
      have := ((hεlim.pow 2).mul_const J |>.const_mul Mdφ).add
        ((hεlim.mul_const I1).const_mul Mφ) |>.const_mul (Mg * ‖v‖)
      simpa using this
    exact squeeze_zero_norm hbd hlim0
  -- `B n → 0` by dominated convergence
  have hBlim : Tendsto B atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := volume)
      (F := fun n x => fderiv ℝ g x v * ((φ x * Z n x : ℝ) : ℂ)) (f := fun _ => (0 : ℂ))
      (fun x => ‖fderiv ℝ g x v * (φ x : ℂ)‖)
      (fun n => (hint_dg _ (hφc.mul (hZc n)) fun x hx => by simp [hφ0 x hx]).aestronglyMeasurable)
      (hint_dg φ hφc hφ0).norm
      (fun n => Eventually.of_forall fun x => by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_mul]
        have h1 : |Z n x| ≤ 1 := by
          rw [abs_of_nonneg (show 0 ≤ Z n x from zeta_nonneg _)]; exact zeta_le_one _
        have := mul_le_mul_of_nonneg_left h1 (abs_nonneg (φ x))
        nlinarith [norm_nonneg (fderiv ℝ g x v), abs_nonneg (φ x)])
      (by
        have hne : ∀ᵐ x ∂(volume : Measure R2), x ≠ y := by
          rw [ae_iff]; simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
          exact measure_singleton y
        filter_upwards [hne] with x hx
        have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
        have hev : ∀ᶠ n in atTop, Z n x = 0 := by
          have := hεlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ‖x - y‖ / 2))
          filter_upwards [this] with n hn
          exact zetaE_eq_zero y (εn n) (hεpos n) x (by linarith)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with n hn
        simp [hn])
    rw [integral_zero] at this
    exact this
  -- conclusion
  have hsum : (∫ x, g x * ((fderiv ℝ φ x v : ℝ) : ℂ)) + ∫ x, fderiv ℝ g x v * (φ x : ℂ) = 0 := by
    have h1 : Tendsto (fun n => A n + B n) atTop
        (𝓝 ((∫ x, g x * ((fderiv ℝ φ x v : ℝ) : ℂ)) + ∫ x, fderiv ℝ g x v * (φ x : ℂ))) :=
      tendsto_const_nhds.congr fun n => hkey n
    have h2 : Tendsto (fun n => A n + B n) atTop (𝓝 0) := by simpa using hAlim.add hBlim
    exact tendsto_nhds_unique h1 h2
  exact (fun a b (h : a + b = 0) => eq_neg_of_add_eq_zero_left h) _ _ hsum
