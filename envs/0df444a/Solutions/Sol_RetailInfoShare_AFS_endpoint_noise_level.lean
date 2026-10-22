-- Prove2me | solution 1 for RetailInfoShare.AFS.endpoint_noise_level
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T14:18:58.464765+00:00
-- url     : https://prove2.me/submissions/8cc0bc67-922e-47d5-982a-aed16c73fcb9

import Mathlib
import Definitions.Def_RetailInfoShare_AFS_Model
import Theorems.Thm_RetailInfoShare_AFS_eq_4
import Theorems.Thm_RetailInfoShare_AFS_eq_5
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RetailInfoShare.AFS.MeanAux

open RetailInfoShare.AFS

variable {P : Params} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma u_memLp (Z : Primitives P Ω μ) : MemLp Z.u 2 μ := by
  have h := Z.law_u
  have hm : MemLp (id : ℝ → ℝ) 2 (μ.map Z.u) := by
    rw [h.map_eq]; exact memLp_id_gaussianReal' 2 (by simp)
  exact (memLp_map_measure_iff aestronglyMeasurable_id h.aemeasurable).1 hm

lemma u_integral (Z : Primitives P Ω μ) : ∫ ω, Z.u ω ∂μ = 0 := by
  rw [Z.law_u.integral_eq, integral_id_gaussianReal]

/-- The "residual demand" `a − b Σ_{d≠i} q_d + u` faced by seller `i`. -/
noncomputable def resid (Z : Primitives P Ω μ) (Q : Fin P.N → Ω → ℝ) (i : Fin P.N) : Ω → ℝ :=
  fun ω => P.a - P.b * ∑ d ∈ Finset.univ.erase i, Q d ω + Z.u ω

lemma resid_memLp (Z : Primitives P Ω μ) (Q : Fin P.N → Ω → ℝ) (hQ : ∀ d, MemLp (Q d) 2 μ)
    (i : Fin P.N) : MemLp (resid Z Q i) 2 μ := by
  haveI := Z.isProb
  have h1 : MemLp (fun ω => ∑ d ∈ Finset.univ.erase i, Q d ω) 2 μ :=
    memLp_finsetSum _ (fun d _ => hQ d)
  exact ((memLp_const P.a).sub (h1.const_mul P.b)).add (u_memLp Z)

lemma resid_integral (Z : Primitives P Ω μ) (Q : Fin P.N → Ω → ℝ) (hQ : ∀ d, MemLp (Q d) 2 μ)
    (i : Fin P.N) :
    ∫ ω, resid Z Q i ω ∂μ = P.a - P.b * ∑ d ∈ Finset.univ.erase i, ∫ ω, Q d ω ∂μ := by
  haveI := Z.isProb
  have hI : ∀ d, Integrable (Q d) μ := fun d => (hQ d).integrable (by norm_num)
  have h1 : Integrable (fun ω => ∑ d ∈ Finset.univ.erase i, Q d ω) μ :=
    integrable_finsetSum _ (fun d _ => hI d)
  have hu : Integrable Z.u μ := (u_memLp Z).integrable (by norm_num)
  have h2 : Integrable (fun ω => P.b * ∑ d ∈ Finset.univ.erase i, Q d ω) μ := h1.const_mul _
  have h3 : Integrable (fun ω => P.a - P.b * ∑ d ∈ Finset.univ.erase i, Q d ω) μ :=
    (integrable_const _).sub h2
  unfold resid
  rw [integral_add h3 hu,
    integral_sub (integrable_const _) h2, integral_const_mul,
    integral_finsetSum _ (fun d _ => hI d), u_integral Z]
  simp

lemma resid_update (Z : Primitives P Ω μ) (Q : Fin P.N → Ω → ℝ) (i : Fin P.N) (q : Ω → ℝ) :
    resid Z (Function.update Q i q) i = resid Z Q i := by
  funext ω
  unfold resid
  congr 3
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hd)]

lemma price_eq (Z : Primitives P Ω μ) (Q : Fin P.N → Ω → ℝ) (i : Fin P.N) :
    price Z Q i = fun ω => resid Z Q i ω - Q i ω := by
  funext ω; unfold price resid; ring

lemma sellerProfit_eq (Z : Primitives P Ω μ) (Q : Fin P.N → Ω → ℝ) (i : Fin P.N) :
    sellerProfit Z Q i = ∫ ω, (1 - P.alpha) * (Q i ω * (resid Z Q i ω - Q i ω)) ∂μ := by
  unfold sellerProfit; rw [price_eq]

lemma sellerProfit_update (Z : Primitives P Ω μ) (Q : Fin P.N → Ω → ℝ) (i : Fin P.N)
    (q : Ω → ℝ) :
    sellerProfit Z (Function.update Q i q) i =
      ∫ ω, (1 - P.alpha) * (q ω * (resid Z Q i ω - q ω)) ∂μ := by
  rw [sellerProfit_eq, resid_update]; simp

/-- Profit of seller `i` playing the constant `c`. -/
lemma sellerProfit_update_const (Z : Primitives P Ω μ) (Q : Fin P.N → Ω → ℝ)
    (hQ : ∀ d, MemLp (Q d) 2 μ) (i : Fin P.N) (c : ℝ) :
    sellerProfit Z (Function.update Q i (fun _ => c)) i =
      (1 - P.alpha) * (c * (∫ ω, resid Z Q i ω ∂μ - c)) := by
  haveI := Z.isProb
  rw [sellerProfit_update]
  have hr : Integrable (resid Z Q i) μ := (resid_memLp Z Q hQ i).integrable (by norm_num)
  rw [integral_const_mul, integral_const_mul, integral_sub hr (integrable_const c)]
  simp

/-- Constant perturbations: in any equilibrium, `2 E[q_i] = E[a − b Σ_{d≠i} q_d + u]`. -/
lemma eq_mean (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (Z : Primitives P Ω μ) (M : NoiseMatrix P.N) (Q : Fin P.N → Ω → ℝ)
    (hQ : IsEquilibrium Z M Q) (i : Fin P.N) :
    2 * ∫ ω, Q i ω ∂μ = ∫ ω, resid Z Q i ω ∂μ := by
  haveI := Z.isProb
  have hL : ∀ d, MemLp (Q d) 2 μ := fun d => (hQ.1 d).2
  set EA := ∫ ω, resid Z Q i ω ∂μ
  set EQ := ∫ ω, Q i ω ∂μ
  set c := (EA - 2 * EQ) / 2
  have hadm : IsAdmissible Z M i (fun ω => Q i ω + c) :=
    ⟨(hQ.1 i).1.add stronglyMeasurable_const, (hQ.1 i).2.add (memLp_const c)⟩
  have hle := hQ.2 i _ hadm
  rw [sellerProfit_update, sellerProfit_eq] at hle
  have hr : MemLp (resid Z Q i) 2 μ := resid_memLp Z Q hL i
  have hQi : MemLp (Q i) 2 μ := hL i
  have i1 : Integrable (fun ω => Q i ω * resid Z Q i ω) μ := hQi.integrable_mul hr
  have i2 : Integrable (fun ω => Q i ω * Q i ω) μ := hQi.integrable_mul hQi
  have iQ : Integrable (Q i) μ := hQi.integrable (by norm_num)
  have iR : Integrable (resid Z Q i) μ := hr.integrable (by norm_num)
  have e1 : (fun ω => (1 - P.alpha) * ((Q i ω + c) * (resid Z Q i ω - (Q i ω + c)))) =
      fun ω => (1 - P.alpha) * (Q i ω * (resid Z Q i ω - Q i ω)) +
        (1 - P.alpha) * (c * resid Z Q i ω - 2 * c * Q i ω - c ^ 2) := by
    funext ω; ring
  have j1 : Integrable (fun ω => (1 - P.alpha) * (Q i ω * (resid Z Q i ω - Q i ω))) μ := by
    have : (fun ω => (1 - P.alpha) * (Q i ω * (resid Z Q i ω - Q i ω))) =
        fun ω => (1 - P.alpha) * (Q i ω * resid Z Q i ω - Q i ω * Q i ω) := by
      funext ω; ring
    rw [this]; exact (i1.sub i2).const_mul _
  have j2 : Integrable (fun ω => (1 - P.alpha) * (c * resid Z Q i ω - 2 * c * Q i ω - c ^ 2))
      μ := (((iR.const_mul c).sub (iQ.const_mul (2 * c))).sub (integrable_const _)).const_mul _
  rw [e1, integral_add j1 j2] at hle
  have hval : ∫ ω, (1 - P.alpha) * (c * resid Z Q i ω - 2 * c * Q i ω - c ^ 2) ∂μ =
      (1 - P.alpha) * (c * EA - 2 * c * EQ - c ^ 2) := by
    have k1 : Integrable (fun ω => c * resid Z Q i ω) μ := iR.const_mul c
    have k2 : Integrable (fun ω => 2 * c * Q i ω) μ := iQ.const_mul (2 * c)
    have k3 : Integrable (fun ω => c * resid Z Q i ω - 2 * c * Q i ω) μ := k1.sub k2
    rw [integral_const_mul, integral_sub k3 (integrable_const _), integral_sub k1 k2,
      integral_const_mul, integral_const_mul]
    simp [EA, EQ]
  rw [hval] at hle
  have ha : 0 < 1 - P.alpha := by linarith [hP.2.2.2.2.2.2]
  have : (1 - P.alpha) * (c * EA - 2 * c * EQ - c ^ 2) ≤ 0 := by linarith
  have hc2 : c * EA - 2 * c * EQ - c ^ 2 = c ^ 2 := by simp only [c]; ring
  rw [hc2] at this
  have : c ^ 2 ≤ 0 := by
    by_contra h; push Not at h; nlinarith
  have : c = 0 := by nlinarith [sq_nonneg c]
  simp only [c] at this
  linarith

/-- The linear system `2 x_i = a − b Σ_{d≠i} x_d` has the unique solution `qNS`. -/
lemma linear_system (P : Params) (hP : P.Standing) (x : Fin P.N → ℝ)
    (hx : ∀ i, 2 * x i = P.a - P.b * ∑ d ∈ Finset.univ.erase i, x d) (i : Fin P.N) :
    x i = qNS P := by
  obtain ⟨hN, hb0, hb1, -⟩ := hP
  set T := ∑ d, x d
  have hx' : ∀ i, (2 - P.b) * x i = P.a - P.b * T := by
    intro i
    have := hx i
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)] at this
    linarith
  have hsum : (2 - P.b) * T = P.N * P.a - P.N * P.b * T := by
    have : ∑ i, (2 - P.b) * x i = ∑ _i : Fin P.N, (P.a - P.b * T) :=
      Finset.sum_congr rfl (fun i _ => hx' i)
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at this
    rw [this]; ring
  have hN' : (1 : ℝ) ≤ P.N := by exact_mod_cast hN
  have hD : 0 < 2 + P.b * ((P.N : ℝ) - 1) := by nlinarith
  have h2b : (2 - P.b) ≠ 0 := by intro h; linarith
  unfold qNS
  rw [eq_div_iff hD.ne']
  have key : (2 - P.b) * (x i * (2 + P.b * ((P.N : ℝ) - 1))) = (2 - P.b) * P.a := by
    have h1 := hx' i
    have : (2 - P.b) * (x i * (2 + P.b * ((P.N : ℝ) - 1))) =
        ((2 - P.b) * x i) * (2 - P.b) + ((2 - P.b) * x i) * (P.b * P.N) := by ring
    rw [this, h1]
    nlinarith [hsum]
  exact mul_left_cancel₀ h2b key

/-- In every equilibrium, every seller's mean quantity is `qNS`. -/
lemma mean_eq_qNS (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (Z : Primitives P Ω μ) (M : NoiseMatrix P.N) (Q : Fin P.N → Ω → ℝ)
    (hQ : IsEquilibrium Z M Q) (i : Fin P.N) : ∫ ω, Q i ω ∂μ = qNS P := by
  refine linear_system P hP (fun i => ∫ ω, Q i ω ∂μ) (fun i => ?_) i
  rw [eq_mean P hP Z M Q hQ i, resid_integral Z Q (fun d => (hQ.1 d).2) i]

lemma info_bot (Z : Primitives P Ω μ) (M : NoiseMatrix P.N) (j : Fin P.N)
    (hj : ∀ i, M i j = ⊤) : info Z M j = ⊥ := by
  simp [info, hj]

/-- An uninformed seller plays the constant `qNS` in every equilibrium. -/
lemma uninformed_const (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (Z : Primitives P Ω μ) (M : NoiseMatrix P.N) (Q : Fin P.N → Ω → ℝ)
    (hQ : IsEquilibrium Z M Q) (j : Fin P.N) (hj : ∀ i, M i j = ⊤) :
    Q j = fun _ => qNS P := by
  haveI := Z.isProb
  have hm := (hQ.1 j).1
  rw [info_bot Z M j hj] at hm
  obtain ⟨c, hc⟩ := stronglyMeasurable_bot_iff.mp hm
  have := mean_eq_qNS P hP Z M Q hQ j
  rw [hc] at this ⊢
  simp at this
  rw [this]

/-- An uninformed seller earns `(1 − α) qNS²` in every equilibrium. -/
lemma uninformed_profit (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (Z : Primitives P Ω μ) (M : NoiseMatrix P.N) (Q : Fin P.N → Ω → ℝ)
    (hQ : IsEquilibrium Z M Q) (j : Fin P.N) (hj : ∀ i, M i j = ⊤) :
    sellerProfit Z Q j = (1 - P.alpha) * qNS P ^ 2 := by
  have hc := uninformed_const P hP Z M Q hQ j hj
  have hmean := eq_mean P hP Z M Q hQ j
  have hQQ : Q = Function.update Q j (fun _ => qNS P) := by
    rw [← hc]; simp
  have hL : ∀ d, MemLp (Q d) 2 μ := fun d => (hQ.1 d).2
  have := sellerProfit_update_const Z Q hL j (qNS P)
  rw [← hQQ] at this
  rw [this, ← hmean, hc]
  haveI := Z.isProb
  simp only [integral_const, probReal_univ, one_smul]; ring

lemma xhat_measurable (Z : Primitives P Ω μ) (M : NoiseMatrix P.N) (i j : Fin P.N) :
    Measurable (xhat Z M i j) := by
  unfold xhat
  exact (Z.meas_u.add (Z.meas_e i)).add ((Z.meas_ξ i j).const_mul _)

lemma info_le (Z : Primitives P Ω μ) (M : NoiseMatrix P.N) (j : Fin P.N) :
    info Z M j ≤ ‹MeasurableSpace Ω› :=
  iSup_le fun i => iSup_le fun _ => (xhat_measurable Z M i j).comap_le

/-- `E[q X] = E[q E[X | G]]` for `G`-measurable square-integrable `q`. -/
lemma integral_mul_condExp {Ω' : Type*} {G m0 : MeasurableSpace Ω'} {μ : Measure[m0] Ω'}
    [IsProbabilityMeasure μ] (hG : G ≤ m0) (q X : Ω' → ℝ) (hq : StronglyMeasurable[G] q)
    (hq2 : MemLp q 2 μ) (hX : MemLp X 2 μ) :
    ∫ ω, q ω * X ω ∂μ = ∫ ω, q ω * (μ[X | G]) ω ∂μ := by
  have hqX : Integrable (q * X) μ := hq2.integrable_mul hX
  have h1 := condExp_mul_of_stronglyMeasurable_left hq hqX (hX.integrable (by norm_num))
  have h2 : ∫ ω, (μ[q * X | G]) ω ∂μ = ∫ ω, (q * X) ω ∂μ := integral_condExp hG
  rw [integral_congr_ae h1] at h2
  simpa using h2.symm

/-- Quadratic decomposition of the expected profit. -/
lemma profit_decomp {Ω' : Type*} {G m0 : MeasurableSpace Ω'} {μ : Measure[m0] Ω'}
    [IsProbabilityMeasure μ] (hG : G ≤ m0) (alpha : ℝ) (A T q : Ω' → ℝ) (hA : MemLp A 2 μ)
    (hT : (fun ω => 2 * T ω) =ᵐ[μ] μ[A | G]) (hTL : MemLp T 2 μ)
    (hq : StronglyMeasurable[G] q) (hqL : MemLp q 2 μ) :
    ∫ ω, (1 - alpha) * (q ω * (A ω - q ω)) ∂μ =
      (1 - alpha) * (∫ ω, T ω ^ 2 ∂μ - ∫ ω, (q ω - T ω) ^ 2 ∂μ) := by
  have e1 := integral_mul_condExp hG q A hq hqL hA
  have e2 : ∫ ω, q ω * (μ[A | G]) ω ∂μ = ∫ ω, q ω * (2 * T ω) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hT] with ω h
    rw [h]
  have iqA : Integrable (fun ω => q ω * A ω) μ := hqL.integrable_mul hA
  have iqq : Integrable (fun ω => q ω * q ω) μ := hqL.integrable_mul hqL
  have iqT : Integrable (fun ω => q ω * T ω) μ := hqL.integrable_mul hTL
  have iTT : Integrable (fun ω => T ω * T ω) μ := hTL.integrable_mul hTL
  have h3 : (fun ω => (1 - alpha) * (q ω * (A ω - q ω))) =
      fun ω => (1 - alpha) * (q ω * A ω - q ω * q ω) := by funext ω; ring
  have h4 : (fun ω => (q ω - T ω) ^ 2) =
      fun ω => q ω * q ω - 2 * (q ω * T ω) + T ω * T ω := by funext ω; ring
  have h5 : (fun ω => T ω ^ 2) = fun ω => T ω * T ω := by funext ω; ring
  have h6 : (fun ω => q ω * (2 * T ω)) = fun ω => 2 * (q ω * T ω) := by funext ω; ring
  have i2 : Integrable (fun ω => 2 * (q ω * T ω)) μ := iqT.const_mul 2
  have i3 : Integrable (fun ω => q ω * q ω - 2 * (q ω * T ω)) μ := iqq.sub i2
  rw [h3, integral_const_mul, integral_sub iqA iqq, e1, e2, h4, h5, h6,
    integral_add i3 iTT, integral_sub iqq i2, integral_const_mul]
  ring

end RetailInfoShare.AFS.MeanAux

namespace RetailInfoShare.AFS.GaussAux

open RetailInfoShare.AFS

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Covariance of two linear combinations of independent centered Gaussians. -/
lemma cov_lin [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : ι → Ω → ℝ) (v : ι → ℝ≥0)
    (hlaw : ∀ k, HasLaw (Y k) (gaussianReal 0 (v k)) μ) (hind : iIndepFun Y μ)
    (α β : ι → ℝ) :
    cov[fun ω => ∑ k, α k * Y k ω, fun ω => ∑ k, β k * Y k ω; μ] =
      ∑ k, α k * β k * (v k : ℝ) := by
  have hmem : ∀ k, MemLp (Y k) 2 μ := fun k =>
    (hlaw k).hasGaussianLaw.memLp_two
  rw [covariance_fun_sum_fun_sum (fun k => (hmem k).const_mul (α k))
    (fun k => (hmem k).const_mul (β k))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_eq_single k]
  · rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_self (hlaw k).aemeasurable, (hlaw k).variance_eq, variance_id_gaussianReal]
    ring
  · intro l _ hlk
    rw [covariance_const_mul_left, covariance_const_mul_right,
      (hind.indepFun (Ne.symm hlk)).covariance_eq_zero (hmem k) (hmem l)]
    ring
  · intro h; exact absurd (Finset.mem_univ k) h

/-- Orthogonal linear combinations of independent centered Gaussians are independent. -/
lemma indep_lin [IsProbabilityMeasure μ] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (Y : ι → Ω → ℝ) (v : ι → ℝ≥0)
    (hlaw : ∀ k, HasLaw (Y k) (gaussianReal 0 (v k)) μ) (hind : iIndepFun Y μ)
    (α : ι → ℝ) (β : κ → ι → ℝ) (horth : ∀ c, ∑ k, α k * β c k * (v k : ℝ) = 0) :
    IndepFun (fun ω => ∑ k, α k * Y k ω) (fun ω c => ∑ k, β c k * Y k ω) μ := by
  have hG : ∀ k, HasGaussianLaw (Y k) μ := fun k => (hlaw k).hasGaussianLaw
  have hJ : HasGaussianLaw (fun ω => (Y · ω)) μ := hind.hasGaussianLaw hG
  let LA : (ι → ℝ) →L[ℝ] ℝ := ∑ k, α k • ContinuousLinearMap.proj k
  let LB : (ι → ℝ) →L[ℝ] (κ → ℝ) :=
    ContinuousLinearMap.pi fun c => ∑ k, β c k • ContinuousLinearMap.proj k
  let L : (ι → ℝ) →L[ℝ] (Unit → ℝ) × (κ → ℝ) :=
    (ContinuousLinearMap.pi fun _ => LA).prod LB
  have hL : (fun ω => L (Y · ω)) =
      fun ω => ((fun _ : Unit => ∑ k, α k * Y k ω), fun c => ∑ k, β c k * Y k ω) := by
    funext ω
    simp [L, LA, LB]
  have hXY := hJ.map_fun L
  rw [hL] at hXY
  have hcov : ∀ (i : Unit) (c : κ),
      cov[fun ω => ∑ k, α k * Y k ω, fun ω => ∑ k, β c k * Y k ω; μ] = 0 := by
    intro _ c
    rw [cov_lin Y v hlaw hind]
    exact horth c
  have h := HasGaussianLaw.indepFun_of_covariance_eval
    (X := fun (_ : Unit) => fun ω => ∑ k, α k * Y k ω)
    (Y := fun c => fun ω => ∑ k, β c k * Y k ω) hXY hcov
  have h2 := h.comp (φ := fun f : Unit → ℝ => f ()) (ψ := id) (show Measurable fun f : Unit → ℝ => f () from measurable_pi_apply ())
    measurable_id
  exact h2

end RetailInfoShare.AFS.GaussAux

namespace RetailInfoShare.AFS.UniqAux

open RetailInfoShare.AFS RetailInfoShare.AFS.MeanAux

/-- Equilibria are unique almost surely, for every noise matrix: the Cournot game is a
potential game with the strictly concave potential `E[Σ(a+u)q_i − Σ q_i² − b Σ_{i<d} q_i q_d]`. -/
lemma eq_unique (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ) (M : NoiseMatrix P.N)
    (Q Q' : Fin P.N → Ω → ℝ) (hQ : IsEquilibrium Z M Q) (hQ' : IsEquilibrium Z M Q') :
    ∀ᵐ ω ∂μ, ∀ i, Q i ω = Q' i ω := by
  haveI := Z.isProb
  have hb0 := hP.2.1
  have hb1 := hP.2.2.1
  have hF := (eq_4 P hP μ Z M Q hQ.1).1 hQ
  have hF' := (eq_4 P hP μ Z M Q' hQ'.1).1 hQ'
  set D : Fin P.N → Ω → ℝ := fun k ω => Q k ω - Q' k ω with hDdef
  have hDL : ∀ k, MemLp (D k) 2 μ := fun k => (hQ.1 k).2.sub (hQ'.1 k).2
  have hDm : ∀ k, StronglyMeasurable[info Z M k] (D k) := fun k => (hQ.1 k).1.sub (hQ'.1 k).1
  have hInt : ∀ k, Integrable (Q k) μ := fun k => ((hQ.1 k).2).integrable (by norm_num)
  have hInt' : ∀ k, Integrable (Q' k) μ := fun k => ((hQ'.1 k).2).integrable (by norm_num)
  -- difference of the first-order conditions
  have hDce : ∀ k d, μ[D d | info Z M k] =ᵐ[μ] fun ω =>
      (μ[Q d | info Z M k]) ω - (μ[Q' d | info Z M k]) ω := by
    intro k d
    have := condExp_sub (hInt d) (hInt' d) (info Z M k) (μ := μ)
    have e : D d = Q d - Q' d := by funext ω; simp [D]
    rw [e]; exact this
  have hD : ∀ k, D k =ᵐ[μ] fun ω =>
      -(P.b / 2) * ∑ d ∈ Finset.univ.erase k, (μ[D d | info Z M k]) ω := by
    intro k
    have hall := ae_all_iff.2 (hDce k)
    filter_upwards [hF k, hF' k, hall] with ω h1 h2 h3
    simp only [D, h1, h2, h3, Finset.sum_sub_distrib]
    ring
  -- E[D_k²] = -(b/2) Σ_{d≠k} E[D_k D_d]
  have hsq : ∀ k, ∫ ω, D k ω * D k ω ∂μ =
      -(P.b / 2) * ∑ d ∈ Finset.univ.erase k, ∫ ω, D k ω * D d ω ∂μ := by
    intro k
    have e1 : ∫ ω, D k ω * D k ω ∂μ = ∫ ω, D k ω * (-(P.b / 2) *
        ∑ d ∈ Finset.univ.erase k, (μ[D d | info Z M k]) ω) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hD k] with ω h
      rw [← h]
    rw [e1]
    have e2 : (fun ω => D k ω * (-(P.b / 2) *
        ∑ d ∈ Finset.univ.erase k, (μ[D d | info Z M k]) ω)) =
        fun ω => -(P.b / 2) * ∑ d ∈ Finset.univ.erase k, D k ω * (μ[D d | info Z M k]) ω := by
      funext ω; rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun d _ => by ring)
    rw [e2, integral_const_mul, integral_finsetSum _ (fun d _ =>
      (show Integrable (fun ω => D k ω * (μ[D d | info Z M k]) ω) μ from
        (hDL k).integrable_mul ((hDL d).condExp (by norm_num))))]
    congr 1
    refine Finset.sum_congr rfl (fun d _ => ?_)
    exact (integral_mul_condExp (info_le Z M k) (D k) (D d) (hDm k) (hDL k) (hDL d)).symm
  -- quadratic form identity
  have hId : ∀ ω, (1 - P.b / 2) * ∑ k, D k ω * D k ω + (P.b / 2) * (∑ k, D k ω) ^ 2 =
      ∑ k, (D k ω * D k ω + (P.b / 2) * ∑ d ∈ Finset.univ.erase k, D k ω * D d ω) := by
    intro ω
    have : (∑ k, D k ω) ^ 2 = ∑ k, (D k ω * D k ω + ∑ d ∈ Finset.univ.erase k, D k ω * D d ω) := by
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    rw [this, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have hpp : ∀ k d, Integrable (fun ω => D k ω * D d ω) μ := fun k d =>
    (hDL k).integrable_mul (hDL d)
  have htot : ∫ ω, ((1 - P.b / 2) * ∑ k, D k ω * D k ω + (P.b / 2) * (∑ k, D k ω) ^ 2) ∂μ = 0 := by
    simp_rw [hId]
    rw [integral_finsetSum _ (fun k _ => (show Integrable (fun ω => D k ω * D k ω +
      (P.b / 2) * ∑ d ∈ Finset.univ.erase k, D k ω * D d ω) μ from (hpp k k).add
      ((integrable_finsetSum _ (fun d _ => hpp k d)).const_mul _)))]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [integral_add (hpp k k) (show Integrable (fun ω => (P.b / 2) *
      ∑ d ∈ Finset.univ.erase k, D k ω * D d ω) μ from
        (integrable_finsetSum _ (fun d _ => hpp k d)).const_mul _),
      integral_const_mul, integral_finsetSum _ (fun d _ => hpp k d), hsq k]
    ring
  have i1 : Integrable (fun ω => ∑ k, D k ω * D k ω) μ :=
    integrable_finsetSum _ (fun k _ => hpp k k)
  have i2 : Integrable (fun ω => (∑ k, D k ω) ^ 2) μ :=
    (memLp_finsetSum _ (fun k _ => hDL k)).integrable_sq
  rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
    integral_const_mul] at htot
  have n1 : 0 ≤ ∫ ω, ∑ k, D k ω * D k ω ∂μ :=
    integral_nonneg (fun ω => Finset.sum_nonneg (fun k _ => mul_self_nonneg _))
  have n2 : 0 ≤ ∫ ω, (∑ k, D k ω) ^ 2 ∂μ := integral_nonneg (fun ω => sq_nonneg _)
  have hz : ∫ ω, ∑ k, D k ω * D k ω ∂μ = 0 := by nlinarith
  rw [integral_finsetSum _ (fun k _ => hpp k k)] at hz
  have hz' := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
    integral_nonneg (fun ω => mul_self_nonneg (D k ω)))).1 hz
  have hae : ∀ k, ∀ᵐ ω ∂μ, D k ω * D k ω = 0 := by
    intro k
    have := (integral_eq_zero_iff_of_nonneg (fun ω => mul_self_nonneg (D k ω)) (hpp k k)).1
      (hz' k (Finset.mem_univ k))
    filter_upwards [this] with ω h
    exact h
  filter_upwards [ae_all_iff.2 hae] with ω h i
  have := mul_self_eq_zero.mp (h i)
  simp only [D] at this
  linarith

end RetailInfoShare.AFS.UniqAux
namespace RetailInfoShare.AFS.AFSAux

open RetailInfoShare.AFS RetailInfoShare.AFS.MeanAux RetailInfoShare.AFS.GaussAux

variable {P : Params} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The AFS matrix with column values `η k`. -/
def colMat (η : Fin P.N → ℝ≥0∞) : NoiseMatrix P.N := fun _ k => η k

/-- Index set of all primitives. -/
abbrev Ix (N : ℕ) := Option (Fin N ⊕ (Fin N × Fin N))

def idxF : Ix P.N → Prim P.N
  | none => .u
  | some (.inl i) => .e i
  | some (.inr p) => .ξ p.1 p.2

lemma idxF_injective : Function.Injective (idxF (P := P)) := by
  intro x y h
  rcases x with _ | x | ⟨x1, x2⟩ <;> rcases y with _ | y | ⟨y1, y2⟩ <;> simp_all [idxF]

def Yf (Z : Primitives P Ω μ) : Ix P.N → Ω → ℝ
  | none => Z.u
  | some (.inl i) => Z.e i
  | some (.inr p) => Z.ξ p.1 p.2

def vf (P : Params) : Ix P.N → ℝ≥0
  | none => P.sig
  | some (.inl _) => P.t
  | some (.inr _) => 1

lemma Yf_law (Z : Primitives P Ω μ) : ∀ x, HasLaw (Yf Z x) (gaussianReal 0 (vf P x)) μ := by
  intro x
  rcases x with _ | i | ⟨i, k⟩
  · exact Z.law_u
  · exact Z.law_e i
  · exact Z.law_ξ i k

lemma Yf_indep (Z : Primitives P Ω μ) : iIndepFun (Yf Z) μ := by
  have h := Z.indep.precomp (idxF_injective (P := P))
  convert h using 2 with x
  rcases x with _ | i | ⟨i, k⟩ <;> rfl

lemma Yf_meas (Z : Primitives P Ω μ) : ∀ x, Measurable (Yf Z x) := by
  intro x
  rcases x with _ | i | ⟨i, k⟩
  · exact Z.meas_u
  · exact Z.meas_e i
  · exact Z.meas_ξ i k

noncomputable def sk (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) : ℝ := Real.sqrt (η k).toReal

/-- Seller `k`'s average received signal `z_k = (1/N) Σ_i x̂_ik`. -/
noncomputable def zz (Z : Primitives P Ω μ) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) : Ω → ℝ :=
  fun ω => (1 / (P.N : ℝ)) * ∑ i, xhat Z (colMat η) i k ω

noncomputable def VV (P : Params) : ℝ := (P.sig : ℝ) + (P.t : ℝ) / P.N

noncomputable def nu (P : Params) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) : ℝ :=
  VV P + sk η k ^ 2 / P.N

noncomputable def kap (P : Params) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) : ℝ :=
  if η k = ⊤ then 0 else VV P / nu P η k

noncomputable def cX (η : Fin P.N → ℝ≥0∞) (i k : Fin P.N) : Ix P.N → ℝ
  | none => 1
  | some (.inl i') => if i' = i then 1 else 0
  | some (.inr p) => if p = (i, k) then sk η k else 0

noncomputable def cZ (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) : Ix P.N → ℝ
  | none => 1
  | some (.inl _) => 1 / (P.N : ℝ)
  | some (.inr p) => if p.2 = k then sk η k / P.N else 0

def cU : Ix P.N → ℝ
  | none => 1
  | some _ => 0

lemma xhat_lin (Z : Primitives P Ω μ) (η : Fin P.N → ℝ≥0∞) (i k : Fin P.N) (ω : Ω) :
    xhat Z (colMat η) i k ω = ∑ x, cX η i k x * Yf Z x ω := by
  classical
  simp [Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_prod_type, cX, Yf, xhat, colMat,
    sk, ite_and]
  ring

lemma zz_lin (Z : Primitives P Ω μ) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) (ω : Ω) :
    zz Z η k ω = ∑ x, cZ η k x * Yf Z x ω := by
  classical
  simp only [zz, xhat, colMat, Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_prod_type,
    cZ, Yf, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  have hN : (P.N : ℝ) ≠ 0 := by
    rcases Nat.eq_zero_or_pos P.N with h | h
    · exact absurd (Fin.elim0 (h ▸ k)) id
    · exact_mod_cast h.ne'
  simp only [sk]
  field_simp
  ring

lemma u_lin (Z : Primitives P Ω μ) (ω : Ω) : Z.u ω = ∑ x, cU x * Yf Z x ω := by
  simp [Fintype.sum_option, Fintype.sum_sum_type, cU, Yf]

lemma NposR (k : Fin P.N) : (0 : ℝ) < P.N := by
  have : 0 < P.N := Fin.pos k
  exact_mod_cast this

lemma sum_cZ_cX (η : Fin P.N → ℝ≥0∞) (d i k : Fin P.N) :
    ∑ x, cZ η d x * cX η i k x * (vf P x : ℝ) =
      VV P + (if d = k then sk η d * sk η k / P.N else 0) := by
  classical
  have hN := NposR k
  simp only [Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_prod_type, cZ, cX, vf,
    NNReal.coe_one, mul_one, Prod.mk.injEq, mul_ite, mul_zero, ite_mul, zero_mul]
  simp only [ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single i]
  · simp only [if_true]
    unfold VV
    by_cases h : k = d
    · subst h; simp; ring
    · simp [h, Ne.symm h]; ring
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma sum_cZ_cZ (η : Fin P.N → ℝ≥0∞) (k d : Fin P.N) :
    ∑ x, cZ η k x * cZ η d x * (vf P x : ℝ) =
      VV P + (if k = d then sk η k ^ 2 / P.N else 0) := by
  classical
  have hN := NposR k
  simp only [Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_prod_type, cZ, vf,
    NNReal.coe_one, mul_one, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold VV
  by_cases h : k = d
  · subst h; simp; field_simp; ring
  · simp [h, Ne.symm h]
    field_simp

lemma sum_cZ_cU (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) :
    ∑ x, cZ η k x * cU x * (vf P x : ℝ) = P.sig := by
  simp [Fintype.sum_option, Fintype.sum_sum_type, cZ, cU, vf]

lemma integral_lin (Z : Primitives P Ω μ) (γ : Ix P.N → ℝ) :
    ∫ ω, ∑ x, γ x * Yf Z x ω ∂μ = 0 := by
  haveI := Z.isProb
  rw [integral_finsetSum _ (fun x _ => ((Yf_law Z x).hasGaussianLaw.integrable).const_mul _)]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  rw [integral_const_mul, (Yf_law Z x).integral_eq, integral_id_gaussianReal, mul_zero]

lemma memLp_lin (Z : Primitives P Ω μ) (γ : Ix P.N → ℝ) :
    MemLp (fun ω => ∑ x, γ x * Yf Z x ω) 2 μ :=
  memLp_finsetSum _ (fun x _ => ((Yf_law Z x).hasGaussianLaw.memLp_two).const_mul _)

lemma meas_lin (Z : Primitives P Ω μ) (γ : Ix P.N → ℝ) :
    Measurable (fun ω => ∑ x, γ x * Yf Z x ω) :=
  Finset.measurable_sum _ (fun x _ => (Yf_meas Z x).const_mul _)

lemma moment_lin (Z : Primitives P Ω μ) (γ δ : Ix P.N → ℝ) :
    ∫ ω, (∑ x, γ x * Yf Z x ω) * (∑ x, δ x * Yf Z x ω) ∂μ =
      ∑ x, γ x * δ x * (vf P x : ℝ) := by
  classical
  haveI := Z.isProb
  have := cov_lin (Yf Z) (vf P) (Yf_law Z) (Yf_indep Z) γ δ
  rw [covariance] at this
  simp only [integral_lin, sub_zero] at this
  exact this

lemma zz_eq (Z : Primitives P Ω μ) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) :
    zz Z η k = fun ω => ∑ x, cZ η k x * Yf Z x ω := funext (zz_lin Z η k)

lemma zz_integral (Z : Primitives P Ω μ) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) :
    ∫ ω, zz Z η k ω ∂μ = 0 := by rw [zz_eq]; exact integral_lin Z _

lemma zz_memLp (Z : Primitives P Ω μ) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) :
    MemLp (zz Z η k) 2 μ := by rw [zz_eq]; exact memLp_lin Z _

lemma zz_zz (Z : Primitives P Ω μ) (η : Fin P.N → ℝ≥0∞) (k d : Fin P.N) :
    ∫ ω, zz Z η k ω * zz Z η d ω ∂μ = VV P + (if k = d then sk η k ^ 2 / P.N else 0) := by
  rw [zz_eq, zz_eq, moment_lin, sum_cZ_cZ]

lemma zz_u (Z : Primitives P Ω μ) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) :
    ∫ ω, zz Z η k ω * Z.u ω ∂μ = P.sig := by
  have hu : Z.u = fun ω => ∑ x, cU x * Yf Z x ω := funext (u_lin Z)
  rw [zz_eq, hu, moment_lin, sum_cZ_cU]

/-- Seller `k`'s information is generated by the vector of his received signals. -/
lemma info_col (Z : Primitives P Ω μ) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) (hk : η k ≠ ⊤) :
    info Z (colMat η) k =
      MeasurableSpace.comap (fun ω i => xhat Z (colMat η) i k ω) MeasurableSpace.pi := by
  unfold info
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  refine iSup_congr (fun i => ?_)
  rw [iSup_pos (by simpa [colMat] using hk), MeasurableSpace.comap_comp]
  rfl

lemma info_col_bot (Z : Primitives P Ω μ) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) (hk : η k = ⊤) :
    info Z (colMat η) k = ⊥ :=
  info_bot Z _ k (fun i => by simp [colMat, hk])

lemma zz_meas_info (Z : Primitives P Ω μ) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) (hk : η k ≠ ⊤) :
    Measurable[info Z (colMat η) k] (zz Z η k) := by
  have hx : ∀ i, Measurable[info Z (colMat η) k] (xhat Z (colMat η) i k) := by
    intro i
    rw [info_col Z η k hk]
    have h1 : Measurable[MeasurableSpace.comap (fun ω c => xhat Z (colMat η) c k ω)
        MeasurableSpace.pi] (fun ω c => xhat Z (colMat η) c k ω) :=
      Measurable.of_comap_le le_rfl
    exact (show Measurable fun f : Fin P.N → ℝ => f i from measurable_pi_apply i).comp h1
  unfold zz
  exact (Finset.measurable_sum _ (fun i _ => hx i)).const_mul _

/-- Splitting a conditional expectation into an independent centered part and a
measurable part. -/
lemma condExp_split {Ω' : Type*} {G m0 : MeasurableSpace Ω'} {μ : Measure[m0] Ω'}
    [IsProbabilityMeasure μ]
    (hG : G ≤ m0) (R h : Ω' → ℝ) (hRm : Measurable[m0] R)
    (hind : Indep (MeasurableSpace.comap R inferInstance) G μ) (hR0 : ∫ ω, R ω ∂μ = 0)
    (hRi : Integrable R μ) (hh : StronglyMeasurable[G] h) (hhi : Integrable h μ) :
    μ[fun ω => R ω + h ω | G] =ᵐ[μ] h := by
  have hcR : μ[R | G] =ᵐ[μ] fun _ => (0 : ℝ) := by
    have := condExp_indep_eq hRm.comap_le hG (Measurable.of_comap_le le_rfl).stronglyMeasurable
      hind
    rw [hR0] at this; exact this
  have hadd := condExp_add hRi hhi G (μ := μ)
  rw [condExp_of_stronglyMeasurable hG hh hhi] at hadd
  have e : (fun ω => R ω + h ω) = R + h := rfl
  rw [e]
  filter_upwards [hadd, hcR] with ω h1 h2
  rw [h1, Pi.add_apply, h2, zero_add]

end RetailInfoShare.AFS.AFSAux
namespace RetailInfoShare.AFS.AFSAux

open RetailInfoShare.AFS RetailInfoShare.AFS.MeanAux RetailInfoShare.AFS.GaussAux

variable {P : Params} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma VV_pos (hP : P.Standing) : 0 < VV P := by
  have hs : (0 : ℝ) < P.sig := NNReal.coe_pos.mpr hP.2.2.2.1
  have ht : (0 : ℝ) < P.t := NNReal.coe_pos.mpr hP.2.2.2.2.1
  have hN : (0 : ℝ) < P.N := by exact_mod_cast hP.1
  unfold VV; positivity

lemma nu_pos (hP : P.Standing) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) : 0 < nu P η k := by
  have hN : (0 : ℝ) < P.N := by exact_mod_cast hP.1
  unfold nu; have := VV_pos hP; positivity

lemma kap_nu (hP : P.Standing) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) (hk : η k ≠ ⊤) :
    kap P η k * nu P η k = VV P := by
  unfold kap; rw [if_neg hk]; field_simp [(nu_pos hP η k).ne']

lemma kap_nonneg (hP : P.Standing) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) : 0 ≤ kap P η k := by
  unfold kap; split_ifs
  · exact le_rfl
  · exact div_nonneg (VV_pos hP).le (nu_pos hP η k).le

lemma kap_le_one (hP : P.Standing) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) : kap P η k ≤ 1 := by
  unfold kap; split_ifs
  · norm_num
  · rw [div_le_one (nu_pos hP η k)]
    unfold nu
    have hN : (0 : ℝ) < P.N := by exact_mod_cast hP.1
    have : 0 ≤ sk η k ^ 2 / P.N := by positivity
    linarith

/-- `E[c₀ + c z_d | y_k] = c₀ + c κ_k z_k` for an informed seller `k ≠ d`. -/
lemma condExp_aff (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (Z : Primitives P Ω μ) (η : Fin P.N → ℝ≥0∞) (k d : Fin P.N)
    (hk : η k ≠ ⊤) (hdk : d ≠ k) (c0 c : ℝ) :
    μ[fun ω => c0 + c * zz Z η d ω | info Z (colMat η) k] =ᵐ[μ]
      fun ω => c0 + c * (kap P η k * zz Z η k ω) := by
  classical
  haveI := Z.isProb
  set κ := kap P η k
  let α : Ix P.N → ℝ := fun x => c * (cZ η d x - κ * cZ η k x)
  have horth : ∀ i, ∑ x, α x * cX η i k x * (vf P x : ℝ) = 0 := by
    intro i
    have e : ∀ x, α x * cX η i k x * (vf P x : ℝ) =
        c * (cZ η d x * cX η i k x * (vf P x : ℝ)) -
          c * κ * (cZ η k x * cX η i k x * (vf P x : ℝ)) := by intro x; simp only [α]; ring
    simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_cZ_cX, if_neg hdk, if_true]
    have := kap_nu hP η k hk
    unfold nu at this
    simp only [κ]
    rw [show sk η k * sk η k = sk η k ^ 2 by ring]
    linear_combination (-c) * this
  have hind := indep_lin (Yf Z) (vf P) (Yf_law Z) (Yf_indep Z) α (fun i => cX η i k) horth
  set R : Ω → ℝ := fun ω => ∑ x, α x * Yf Z x ω with hR
  have hRe : R = fun ω => c * (zz Z η d ω - κ * zz Z η k ω) := by
    funext ω
    rw [zz_lin, zz_lin]
    simp only [hR, α]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => by ring)
  have hXe : (fun ω i => ∑ x, cX η i k x * Yf Z x ω) = fun ω i => xhat Z (colMat η) i k ω := by
    funext ω i; rw [xhat_lin]
  rw [hXe] at hind
  have hsplit : (fun ω => c0 + c * zz Z η d ω) =
      fun ω => R ω + (c0 + c * (κ * zz Z η k ω)) := by
    funext ω; rw [hRe]; ring
  rw [hsplit]
  have hzm := zz_meas_info Z η k hk
  refine condExp_split (info_le Z _ k) R _ (meas_lin Z α) ?_ (integral_lin Z α)
    ((memLp_lin Z α).integrable (by norm_num))
    ((measurable_const.add ((hzm.const_mul κ).const_mul c)).stronglyMeasurable)
    ((integrable_const _).add
      ((((zz_memLp Z η k).integrable (by norm_num)).const_mul κ).const_mul c))
  rw [info_col Z η k hk]
  exact hind

/-- Posterior mean of `u` for an informed seller (eq. (5)). -/
lemma posterior_col (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (Z : Primitives P Ω μ) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N)
    (hk : η k ≠ ⊤) :
    μ[Z.u | info Z (colMat η) k] =ᵐ[μ] fun ω => ((P.sig : ℝ) / nu P η k) * zz Z η k ω := by
  have h := eq_5 P hP μ Z (colMat η) k (η k).toNNReal
    (fun i => by simp [colMat, ENNReal.coe_toNNReal hk])
  filter_upwards [h] with ω hω
  rw [hω]
  have e : ((P.sig : ℝ) + ((P.t : ℝ) + ((η k).toNNReal : ℝ)) / P.N) = nu P η k := by
    unfold nu VV sk
    rw [Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.coe_toNNReal_eq_toReal]
    ring
  rw [e]
  rfl

/-! ### The candidate equilibrium -/

noncomputable def ww (P : Params) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) : ℝ :=
  kap P η k / (2 - P.b * kap P η k)

noncomputable def hh (P : Params) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) : ℝ :=
  kap P η k / (2 - P.b * kap P η k) ^ 2

noncomputable def WW (P : Params) (η : Fin P.N → ℝ≥0∞) : ℝ := ∑ k, ww P η k

noncomputable def HH (P : Params) (η : Fin P.N → ℝ≥0∞) : ℝ := ∑ k, hh P η k

noncomputable def cc (P : Params) (η : Fin P.N → ℝ≥0∞) : ℝ :=
  ((P.sig : ℝ) / VV P) / (1 + P.b * WW P η)

noncomputable def bet (P : Params) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) : ℝ :=
  cc P η * ww P η k

noncomputable def Qa (Z : Primitives P Ω μ) (η : Fin P.N → ℝ≥0∞) : Fin P.N → Ω → ℝ :=
  fun k ω => qNS P + bet P η k * zz Z η k ω

lemma two_sub_pos (hP : P.Standing) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) :
    0 < 2 - P.b * kap P η k := by
  have := kap_le_one hP η k
  have := kap_nonneg hP η k
  have hb1 := hP.2.2.1
  have hb0 := hP.2.1
  nlinarith

lemma ww_nonneg (hP : P.Standing) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) : 0 ≤ ww P η k :=
  div_nonneg (kap_nonneg hP η k) (two_sub_pos hP η k).le

lemma hh_nonneg (hP : P.Standing) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) : 0 ≤ hh P η k :=
  div_nonneg (kap_nonneg hP η k) (sq_nonneg _)

lemma WW_nonneg (hP : P.Standing) (η : Fin P.N → ℝ≥0∞) : 0 ≤ WW P η :=
  Finset.sum_nonneg (fun k _ => ww_nonneg hP η k)

lemma one_add_bW_pos (hP : P.Standing) (η : Fin P.N → ℝ≥0∞) : 0 < 1 + P.b * WW P η := by
  have := WW_nonneg hP η
  have := hP.2.1
  positivity

lemma ww_two (hP : P.Standing) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) :
    ww P η k * (2 - P.b * kap P η k) = kap P η k := by
  unfold ww; rw [div_mul_cancel₀ _ (two_sub_pos hP η k).ne']

lemma hh_ww (hP : P.Standing) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) :
    2 * hh P η k = ww P η k + P.b * ww P η k ^ 2 := by
  unfold hh ww
  have := (two_sub_pos hP η k).ne'
  field_simp
  ring

lemma kap_top (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) (hk : η k = ⊤) : kap P η k = 0 := by
  simp [kap, hk]

lemma bet_top (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) (hk : η k = ⊤) : bet P η k = 0 := by
  simp [bet, ww, kap_top η k hk]

lemma Qa_top (Z : Primitives P Ω μ) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) (hk : η k = ⊤) :
    Qa Z η k = fun _ => qNS P := by
  funext ω; simp [Qa, bet_top η k hk]

lemma cc_eq (hP : P.Standing) (η : Fin P.N → ℝ≥0∞) :
    cc P η * (1 + P.b * WW P η) = (P.sig : ℝ) / VV P := by
  unfold cc; field_simp [(one_add_bW_pos hP η).ne']

/-- The key identity behind the first-order condition of an informed seller. -/
lemma foc_key (hP : P.Standing) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) (hk : η k ≠ ⊤) :
    2 * bet P η k + P.b * kap P η k * (∑ d, bet P η d - bet P η k) =
      (P.sig : ℝ) / nu P η k := by
  have h1 := ww_two hP η k
  have h2 := cc_eq hP η
  have h3 := kap_nu hP η k hk
  have hS : ∑ d, bet P η d = cc P η * WW P η := by
    unfold bet WW; rw [Finset.mul_sum]
  rw [hS]
  unfold bet
  have hnu := (nu_pos hP η k).ne'
  have hV := (VV_pos hP).ne'
  have hκ : kap P η k ≠ 0 := by
    intro h; rw [h, zero_mul] at h3; exact hV h3.symm
  have : (P.sig : ℝ) / nu P η k = (P.sig : ℝ) / VV P * kap P η k := by
    rw [← h3]; field_simp
  rw [this, ← h2]
  linear_combination (cc P η) * h1

lemma Qa_memLp (Z : Primitives P Ω μ) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) :
    MemLp (Qa Z η k) 2 μ := by
  haveI := Z.isProb
  have h1 : MemLp (fun ω => bet P η k * zz Z η k ω) 2 μ := (zz_memLp Z η k).const_mul _
  have h2 : MemLp (fun ω => qNS P + bet P η k * zz Z η k ω) 2 μ :=
    (memLp_const (qNS P)).add h1
  unfold Qa
  exact h2

lemma Qa_integral (Z : Primitives P Ω μ) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) :
    ∫ ω, Qa Z η k ω ∂μ = qNS P := by
  haveI := Z.isProb
  show ∫ ω, (qNS P + bet P η k * zz Z η k ω) ∂μ = qNS P
  rw [integral_add (integrable_const _)
    (((zz_memLp Z η k).integrable (by norm_num)).const_mul _), integral_const_mul,
    zz_integral]
  simp

lemma Qa_equilibrium (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ) (η : Fin P.N → ℝ≥0∞) :
    IsEquilibrium Z (colMat η) (Qa Z η) := by
  classical
  haveI := Z.isProb
  have hb0 := hP.2.1
  have hb1 := hP.2.2.1
  have hN' : (1 : ℝ) ≤ P.N := by exact_mod_cast hP.1
  have hD0 : 0 < 2 + P.b * ((P.N : ℝ) - 1) := by nlinarith
  have hq : qNS P * (2 + P.b * ((P.N : ℝ) - 1)) = P.a := by unfold qNS; field_simp
  have hadm : ∀ k, IsAdmissible Z (colMat η) k (Qa Z η k) := by
    intro k
    refine ⟨?_, Qa_memLp Z η k⟩
    by_cases hk : η k = ⊤
    · rw [Qa_top Z η k hk]; exact stronglyMeasurable_const
    · exact (measurable_const.add ((zz_meas_info Z η k hk).const_mul _)).stronglyMeasurable
  refine (eq_4 P hP μ Z _ (Qa Z η) hadm).2 (fun i => ?_)
  by_cases hi : η i = ⊤
  · have hbot := info_col_bot Z η i hi
    have hc : ∀ d, μ[Qa Z η d | info Z (colMat η) i] = fun _ => qNS P := by
      intro d
      rw [hbot, condExp_bot', Qa_integral Z η d]
      simp
    have hcu : μ[Z.u | info Z (colMat η) i] = fun _ => 0 := by
      rw [hbot, condExp_bot', u_integral Z]
      simp
    refine Filter.Eventually.of_forall (fun ω => ?_)
    simp only [hc, hcu, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Nat.cast_sub hP.1, Nat.cast_one, Qa_top Z η i hi, ← hq]
    ring
  · have hall : ∀ d, ∀ᵐ ω ∂μ, d ≠ i → (μ[Qa Z η d | info Z (colMat η) i]) ω =
        qNS P + bet P η d * (kap P η i * zz Z η i ω) := by
      intro d
      by_cases hd : d = i
      · exact Filter.Eventually.of_forall (fun ω h => absurd hd h)
      · filter_upwards [condExp_aff P hP Z η i d hi hd (qNS P) (bet P η d)] with ω hω _
        exact hω
    filter_upwards [ae_all_iff.2 hall, posterior_col P hP Z η i hi] with ω h1 h2
    rw [h2, Finset.sum_congr rfl (fun d hd => h1 d (Finset.ne_of_mem_erase hd))]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul,
      Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    rw [Nat.cast_sub hP.1, Nat.cast_one]
    have hk := foc_key hP η i hi
    show qNS P + bet P η i * zz Z η i ω = _
    rw [← hq, ← hk]
    ring

end RetailInfoShare.AFS.AFSAux
namespace RetailInfoShare.AFS.AFSAux

open RetailInfoShare.AFS RetailInfoShare.AFS.MeanAux RetailInfoShare.AFS.GaussAux

variable {P : Params} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma ww_sq_nu (hP : P.Standing) (η : Fin P.N → ℝ≥0∞) (k : Fin P.N) :
    ww P η k ^ 2 * nu P η k = VV P * hh P η k := by
  by_cases hk : η k = ⊤
  · simp [ww, hh, kap_top η k hk]
  · have h3 := kap_nu hP η k hk
    have h2 := (two_sub_pos hP η k).ne'
    unfold ww hh
    rw [← h3]
    field_simp
    try ring

/-- Closed form of the platform's profit at the AFS candidate. -/
lemma profit_Qa (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ) (η : Fin P.N → ℝ≥0∞) :
    platformProfit Z (Qa Z η) =
      PiNS P + P.alpha * ((P.sig : ℝ) ^ 2 / VV P) * (HH P η / (1 + P.b * WW P η) ^ 2) := by
  classical
  haveI := Z.isProb
  have hb0 := hP.2.1
  have hb1 := hP.2.2.1
  have hN' : (1 : ℝ) ≤ P.N := by exact_mod_cast hP.1
  have hD0 : 0 < 2 + P.b * ((P.N : ℝ) - 1) := by nlinarith
  have hq : qNS P * (2 + P.b * ((P.N : ℝ) - 1)) = P.a := by unfold qNS; field_simp
  set q0 := qNS P with hq0
  set Y : Fin P.N → Ω → ℝ := fun k ω => bet P η k * zz Z η k ω with hY
  set S : Ω → ℝ := fun ω => ∑ k, Y k ω with hS
  -- pointwise integrand
  have hpt : ∀ ω, P.alpha * ∑ i, Qa Z η i ω * price Z (Qa Z η) i ω =
      P.alpha * (P.N * q0 ^ 2) + (P.alpha * (P.N * q0)) * Z.u ω +
        (P.alpha * (q0 * P.b * (1 - P.N))) * S ω + P.alpha * (S ω * Z.u ω) -
        (P.alpha * (1 - P.b)) * ∑ k, Y k ω * Y k ω - (P.alpha * P.b) * (S ω * S ω) := by
    intro ω
    have hsumQ : ∑ d, Qa Z η d ω = P.N * q0 + S ω := by
      simp only [Qa, hS, hY, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rfl
    have hterm : ∀ i, Qa Z η i ω * price Z (Qa Z η) i ω =
        q0 * (q0 + Z.u ω - P.b * S ω) + (q0 + Z.u ω - P.b * S ω) * Y i ω -
          (1 - P.b) * q0 * Y i ω - (1 - P.b) * (Y i ω * Y i ω) := by
      intro i
      unfold price
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hsumQ, ← hq]
      simp only [Qa, hY]
      ring
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [hS]
    ring
  -- integrability
  have hzL := zz_memLp Z η
  have hu := u_memLp Z
  have iS : Integrable S μ := by
    have : S = fun ω => ∑ k, bet P η k * zz Z η k ω := rfl
    rw [this]
    exact integrable_finsetSum _ (fun k _ => ((hzL k).integrable (by norm_num)).const_mul _)
  have SL : MemLp S 2 μ := memLp_finsetSum _ (fun k _ => (hzL k).const_mul (bet P η k))
  have iU : Integrable Z.u μ := hu.integrable (by norm_num)
  have iSU : Integrable (fun ω => S ω * Z.u ω) μ := SL.integrable_mul hu
  have iYY : ∀ k, Integrable (fun ω => Y k ω * Y k ω) μ := fun k =>
    ((hzL k).const_mul (bet P η k)).integrable_mul ((hzL k).const_mul (bet P η k))
  have iSS : Integrable (fun ω => S ω * S ω) μ := SL.integrable_mul SL
  -- moments
  have mS : ∫ ω, S ω ∂μ = 0 := by
    have : S = fun ω => ∑ k, bet P η k * zz Z η k ω := rfl
    rw [this, integral_finsetSum _ (fun k _ => ((hzL k).integrable (by norm_num)).const_mul _)]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [integral_const_mul, zz_integral, mul_zero]
  have mSU : ∫ ω, S ω * Z.u ω ∂μ = (P.sig : ℝ) * ∑ k, bet P η k := by
    have : (fun ω => S ω * Z.u ω) = fun ω => ∑ k, bet P η k * (zz Z η k ω * Z.u ω) := by
      funext ω; simp only [hS, hY, Finset.sum_mul]; exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [this, integral_finsetSum _ (fun k _ => (show Integrable
      (fun ω => bet P η k * (zz Z η k ω * Z.u ω)) μ from
        ((hzL k).integrable_mul hu).const_mul _)), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [integral_const_mul, zz_u]; ring
  have mYY : ∑ k, ∫ ω, Y k ω * Y k ω ∂μ = ∑ k, bet P η k ^ 2 * nu P η k := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have : (fun ω => Y k ω * Y k ω) = fun ω => bet P η k ^ 2 * (zz Z η k ω * zz Z η k ω) := by
      funext ω; simp only [hY]; ring
    rw [this, integral_const_mul, zz_zz, if_pos rfl]
    rfl
  have mSS : ∫ ω, S ω * S ω ∂μ =
      VV P * (∑ k, bet P η k) ^ 2 + ∑ k, bet P η k ^ 2 * (sk η k ^ 2 / P.N) := by
    have : (fun ω => S ω * S ω) =
        fun ω => ∑ k, ∑ d, bet P η k * bet P η d * (zz Z η k ω * zz Z η d ω) := by
      funext ω; simp only [hS, hY, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun d _ => by ring))
    have iKD : ∀ k d, Integrable (fun ω => bet P η k * bet P η d *
        (zz Z η k ω * zz Z η d ω)) μ := fun k d =>
      ((hzL k).integrable_mul (hzL d)).const_mul _
    rw [this, integral_finsetSum _ (fun k _ => (show Integrable (fun ω => ∑ d,
      bet P η k * bet P η d * (zz Z η k ω * zz Z η d ω)) μ from
        integrable_finsetSum _ (fun d _ => iKD k d)))]
    have e2 : ∀ k, ∫ ω, ∑ d, bet P η k * bet P η d * (zz Z η k ω * zz Z η d ω) ∂μ =
        ∑ d, ∫ ω, bet P η k * bet P η d * (zz Z η k ω * zz Z η d ω) ∂μ := fun k =>
      integral_finsetSum _ (fun d _ => iKD k d)
    simp_rw [e2, integral_const_mul, zz_zz, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun d _ => by ring)
    · exact Finset.sum_congr rfl (fun k _ => by ring)
  -- integrate
  unfold platformProfit
  simp_rw [hpt]
  have j1 : Integrable (fun ω => P.alpha * (P.N * q0 ^ 2) + (P.alpha * (P.N * q0)) * Z.u ω) μ :=
    (integrable_const _).add (iU.const_mul _)
  have j2 : Integrable (fun ω => P.alpha * (P.N * q0 ^ 2) + (P.alpha * (P.N * q0)) * Z.u ω +
      (P.alpha * (q0 * P.b * (1 - P.N))) * S ω) μ := j1.add (iS.const_mul _)
  have j3 : Integrable (fun ω => P.alpha * (P.N * q0 ^ 2) + (P.alpha * (P.N * q0)) * Z.u ω +
      (P.alpha * (q0 * P.b * (1 - P.N))) * S ω + P.alpha * (S ω * Z.u ω)) μ :=
    j2.add (iSU.const_mul _)
  have iYs : Integrable (fun ω => ∑ k, Y k ω * Y k ω) μ :=
    integrable_finsetSum _ (fun k _ => iYY k)
  have j4 : Integrable (fun ω => P.alpha * (P.N * q0 ^ 2) + (P.alpha * (P.N * q0)) * Z.u ω +
      (P.alpha * (q0 * P.b * (1 - P.N))) * S ω + P.alpha * (S ω * Z.u ω) -
      (P.alpha * (1 - P.b)) * ∑ k, Y k ω * Y k ω) μ := j3.sub (iYs.const_mul _)
  rw [integral_sub j4 (iSS.const_mul _), integral_sub j3 (iYs.const_mul _),
    integral_add j2 (iSU.const_mul _), integral_add j1 (iS.const_mul _),
    integral_add (integrable_const _) (iU.const_mul _)]
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul, u_integral Z, mS,
    mSU, mSS, integral_finsetSum _ (fun k _ => iYY k), mYY]
  -- algebra
  have hB : ∑ k, bet P η k = cc P η * WW P η := by unfold bet WW; rw [Finset.mul_sum]
  have hBn : ∑ k, bet P η k ^ 2 * nu P η k = cc P η ^ 2 * (VV P * HH P η) := by
    unfold bet HH; rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← ww_sq_nu hP η k]; ring
  have hBs : ∑ k, bet P η k ^ 2 * (sk η k ^ 2 / P.N) =
      ∑ k, bet P η k ^ 2 * nu P η k - VV P * ∑ k, bet P η k ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold nu; ring
  have hB2 : ∑ k, bet P η k ^ 2 = cc P η ^ 2 * ∑ k, ww P η k ^ 2 := by
    unfold bet; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
  have hX : P.b * ∑ k, ww P η k ^ 2 = 2 * HH P η - WW P η := by
    have : ∑ k, 2 * hh P η k = ∑ k, (ww P η k + P.b * ww P η k ^ 2) :=
      Finset.sum_congr rfl (fun k _ => hh_ww hP η k)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum] at this
    unfold HH WW; linarith
  have hV := (VV_pos hP).ne'
  have hcc : VV P * (cc P η * (1 + P.b * WW P η)) = P.sig := by
    rw [cc_eq hP η]; field_simp
  have hR : (P.sig : ℝ) ^ 2 / VV P * (HH P η / (1 + P.b * WW P η) ^ 2) =
      cc P η ^ 2 * VV P * HH P η := by
    unfold cc; have := (one_add_bW_pos hP η).ne'; field_simp
  have hPi : PiNS P = P.alpha * (P.N * q0 ^ 2) := by
    unfold PiNS; rw [← hq]; field_simp
  rw [show P.alpha * ((P.sig : ℝ) ^ 2 / VV P) * (HH P η / (1 + P.b * WW P η) ^ 2) =
    P.alpha * (cc P η ^ 2 * VV P * HH P η) by rw [mul_assoc, hR], hPi, hBs, hBn, hB, hB2]
  linear_combination (P.alpha * VV P * cc P η ^ 2) * hX - (P.alpha * cc P η * WW P η) * hcc

end RetailInfoShare.AFS.AFSAux
namespace RetailInfoShare.AFS.AFSAux

open RetailInfoShare.AFS RetailInfoShare.AFS.MeanAux RetailInfoShare.AFS.UniqAux

variable {P : Params}

/-- The profit gain as a function of one seller's weight `w`, others fixed. -/
noncomputable def Fg (b H0 W0 x : ℝ) : ℝ := (H0 + (x + b * x ^ 2) / 2) / (1 + b * (W0 + x)) ^ 2

/-- An interior weight is strictly beaten by one of the endpoints `0`, `1/(2−b)`. -/
lemma endpoint_real (b H0 W0 w : ℝ) (hb0 : 0 < b) (hb1 : b ≤ 1) (hH : 0 ≤ H0)
    (hW : 0 ≤ W0) (hw0 : 0 < w) (hw1 : w < 1 / (2 - b)) :
    Fg b H0 W0 w < Fg b H0 W0 0 ∨ Fg b H0 W0 w < Fg b H0 W0 (1 / (2 - b)) := by
  set c0 := 1 + b * W0 with hc0
  have hc1 : 1 ≤ c0 := by have := mul_nonneg hb0.le hW; linarith
  set β1 := (1 - 2 * c0) / (2 * b) with hβ1
  set β0 := H0 + c0 * (c0 - 1) / (2 * b) with hβ0
  have hβ0nn : 0 ≤ β0 := by
    have : 0 ≤ c0 * (c0 - 1) / (2 * b) := div_nonneg (by nlinarith) (by linarith)
    linarith
  have hβ1neg : β1 < 0 := by rw [hβ1]; apply div_neg_of_neg_of_pos <;> linarith
  -- the substitution t = 1 / (c0 + b x)
  have hrep : ∀ x : ℝ, 0 ≤ x →
      Fg b H0 W0 x = 1 / (2 * b) + β1 * (1 / (c0 + b * x)) + β0 * (1 / (c0 + b * x)) ^ 2 := by
    intro x hx
    have hs : 0 < c0 + b * x := by nlinarith
    unfold Fg
    rw [show 1 + b * (W0 + x) = c0 + b * x by rw [hc0]; ring, hβ1, hβ0]
    field_simp
    ring
  have h2b : 0 < 2 - b := by linarith
  set w1 := 1 / (2 - b) with hw1def
  have hw1pos : 0 < w1 := by positivity
  set t0 := 1 / (c0 + b * 0) with ht0
  set tw := 1 / (c0 + b * w) with htw
  set t1 := 1 / (c0 + b * w1) with ht1
  have hsw : 0 < c0 + b * w := by nlinarith
  have hs1 : 0 < c0 + b * w1 := by nlinarith
  have htw0 : tw < t0 := by
    rw [htw, ht0]; apply one_div_lt_one_div_of_lt (by nlinarith); nlinarith
  have ht1w : t1 < tw := by
    rw [htw, ht1]; apply one_div_lt_one_div_of_lt hsw; nlinarith
  rw [hrep w hw0.le, hrep 0 le_rfl, hrep w1 hw1pos.le]
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hB⟩ := hcon
  -- hA : f(t0) ≤ f(tw), hB : f(t1) ≤ f(tw)
  have hA' : (tw - t0) * (β1 + β0 * (tw + t0)) ≥ 0 := by nlinarith
  have hB' : (tw - t1) * (β1 + β0 * (tw + t1)) ≥ 0 := by nlinarith
  have hA'' : β1 + β0 * (tw + t0) ≤ 0 := by
    by_contra h; push Not at h; nlinarith
  have hB'' : β1 + β0 * (tw + t1) ≥ 0 := by
    by_contra h; push Not at h; nlinarith
  have : β0 * (t1 - t0) ≥ 0 := by linarith
  have hb0z : β0 = 0 := by nlinarith
  rw [hb0z] at hB''
  linarith

lemma ww_update_ne (η : Fin P.N → ℝ≥0∞) (j k : Fin P.N) (ζ : ℝ≥0∞) (h : k ≠ j) :
    ww P (Function.update η j ζ) k = ww P η k := by
  simp [ww, kap, nu, sk, Function.update_of_ne h]

lemma hh_update_ne (η : Fin P.N → ℝ≥0∞) (j k : Fin P.N) (ζ : ℝ≥0∞) (h : k ≠ j) :
    hh P (Function.update η j ζ) k = hh P η k := by
  simp [hh, kap, nu, sk, Function.update_of_ne h]

lemma gain_update (hP : P.Standing) (η : Fin P.N → ℝ≥0∞) (j : Fin P.N) (ζ : ℝ≥0∞) :
    HH P (Function.update η j ζ) / (1 + P.b * WW P (Function.update η j ζ)) ^ 2 =
      Fg P.b (∑ k ∈ Finset.univ.erase j, hh P η k) (∑ k ∈ Finset.univ.erase j, ww P η k)
        (ww P (Function.update η j ζ) j) := by
  unfold HH WW Fg
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  rw [Finset.sum_congr rfl (fun k hk => hh_update_ne η j k ζ (Finset.ne_of_mem_erase hk)),
    Finset.sum_congr rfl (fun k hk => ww_update_ne η j k ζ (Finset.ne_of_mem_erase hk))]
  have := hh_ww hP (Function.update η j ζ) j
  rw [show hh P (Function.update η j ζ) j =
    (ww P (Function.update η j ζ) j + P.b * ww P (Function.update η j ζ) j ^ 2) / 2 by
      linarith]
  ring

end RetailInfoShare.AFS.AFSAux

open RetailInfoShare.AFS RetailInfoShare.AFS.MeanAux RetailInfoShare.AFS.UniqAux
  RetailInfoShare.AFS.AFSAux in
theorem solution (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ)
    (M : NoiseMatrix P.N) (hM : IsAFS M) (j : Fin P.N) (η : ℝ≥0∞) (hη0 : η ≠ 0) (hηtop : η ≠ ⊤)
    (Q : Fin P.N → Ω → ℝ) (hQ : IsEquilibrium Z (setColumn M j η) Q) :
    ∃ η' : ℝ≥0∞, (η' = 0 ∨ η' = ⊤) ∧ ∃ Q' : Fin P.N → Ω → ℝ,
      IsEquilibrium Z (setColumn M j η') Q' ∧ platformProfit Z Q < platformProfit Z Q' := by
  classical
  have hb0 := hP.2.1
  have hb1 := hP.2.2.1
  set ηv : Fin P.N → ℝ≥0∞ := fun k => M k k with hηv
  have hset : ∀ ζ, setColumn M j ζ = colMat (Function.update ηv j ζ) := by
    intro ζ
    funext i k
    unfold setColumn colMat
    by_cases h : k = j
    · subst h; simp
    · rw [if_neg h, Function.update_of_ne h]; exact hM i k k
  -- profit of any equilibrium of an AFS column vector
  have hprof : ∀ ζ (Q₁ : Fin P.N → Ω → ℝ),
      IsEquilibrium Z (colMat (Function.update ηv j ζ)) Q₁ →
      platformProfit Z Q₁ = PiNS P + P.alpha * ((P.sig : ℝ) ^ 2 / VV P) *
        Fg P.b (∑ k ∈ Finset.univ.erase j, hh P ηv k) (∑ k ∈ Finset.univ.erase j, ww P ηv k)
          (ww P (Function.update ηv j ζ) j) := by
    intro ζ Q₁ hQ₁
    have hu := eq_unique P hP μ Z _ Q₁ _ hQ₁ (Qa_equilibrium P hP μ Z (Function.update ηv j ζ))
    have : platformProfit Z Q₁ = platformProfit Z (Qa Z (Function.update ηv j ζ)) := by
      unfold platformProfit
      refine integral_congr_ae ?_
      filter_upwards [hu] with ω hω
      simp only [price, hω]
    rw [this, profit_Qa P hP μ Z, gain_update hP]
  set H0 := ∑ k ∈ Finset.univ.erase j, hh P ηv k
  set W0 := ∑ k ∈ Finset.univ.erase j, ww P ηv k
  have hH0 : 0 ≤ H0 := Finset.sum_nonneg (fun k _ => hh_nonneg hP ηv k)
  have hW0 : 0 ≤ W0 := Finset.sum_nonneg (fun k _ => ww_nonneg hP ηv k)
  -- the three weights of seller j
  have hwT : ww P (Function.update ηv j ⊤) j = 0 := by
    simp [ww, kap]
  have hw0' : ww P (Function.update ηv j 0) j = 1 / (2 - P.b) := by
    have hV := (VV_pos hP).ne'
    simp [ww, kap, nu, sk, hV]
  have hwη : 0 < ww P (Function.update ηv j η) j ∧ ww P (Function.update ηv j η) j < 1 / (2 - P.b) := by
    have hV := VV_pos hP
    have hN : (0 : ℝ) < P.N := by exact_mod_cast hP.1
    have hr : 0 < η.toReal := ENNReal.toReal_pos hη0 hηtop
    have hk : kap P (Function.update ηv j η) j = VV P / (VV P + η.toReal / P.N) := by
      simp [kap, nu, sk, hηtop, Real.sq_sqrt ENNReal.toReal_nonneg]
    have hκ0 : 0 < kap P (Function.update ηv j η) j := by rw [hk]; positivity
    have hκ1 : kap P (Function.update ηv j η) j < 1 := by
      rw [hk, div_lt_one (by positivity)]
      have : 0 < η.toReal / P.N := by positivity
      linarith
    have h2 := two_sub_pos hP (Function.update ηv j η) j
    unfold ww
    constructor
    · exact div_pos hκ0 h2
    · rw [div_lt_div_iff₀ h2 (by linarith)]
      nlinarith
  have hpos : 0 < P.alpha * ((P.sig : ℝ) ^ 2 / VV P) := by
    have ha := hP.2.2.2.2.2.1
    have hs : (0 : ℝ) < P.sig := NNReal.coe_pos.mpr hP.2.2.2.1
    have := VV_pos hP
    positivity
  rw [hset η] at hQ
  rw [hprof η Q hQ]
  rcases endpoint_real P.b H0 W0 _ hb0 hb1 hH0 hW0 hwη.1 hwη.2 with h | h
  · refine ⟨⊤, Or.inr rfl, Qa Z (Function.update ηv j ⊤), ?_, ?_⟩
    · rw [hset ⊤]; exact Qa_equilibrium P hP μ Z _
    · rw [hprof ⊤ _ (Qa_equilibrium P hP μ Z _), hwT]
      have := mul_lt_mul_of_pos_left h hpos
      linarith
  · refine ⟨0, Or.inl rfl, Qa Z (Function.update ηv j 0), ?_, ?_⟩
    · rw [hset 0]; exact Qa_equilibrium P hP μ Z _
    · rw [hprof 0 _ (Qa_equilibrium P hP μ Z _), hw0']
      have := mul_lt_mul_of_pos_left h hpos
      linarith
