-- Prove2me | solution 1 for RetailInfoShare.AFS.uninformed_seller_benchmark
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T13:40:34.756992+00:00
-- url     : https://prove2.me/submissions/44369c1c-7d97-4f51-ae46-95bde5b8a7c2

import Mathlib
import Definitions.Def_RetailInfoShare_AFS_Model
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

end RetailInfoShare.AFS.MeanAux

open RetailInfoShare.AFS RetailInfoShare.AFS.MeanAux in
theorem solution (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ)
    (M : NoiseMatrix P.N) (Q Q₀ : Fin P.N → Ω → ℝ) (hQ : IsEquilibrium Z M Q)
    (hQ₀ : IsEquilibrium Z (noSharing P.N) Q₀) (j : Fin P.N) (hj : ∀ i, M i j = ⊤) :
    sellerProfit Z Q j = sellerProfit Z Q₀ j := by
  rw [uninformed_profit P hP Z M Q hQ j hj,
    uninformed_profit P hP Z (noSharing P.N) Q₀ hQ₀ j (fun _ => rfl)]
