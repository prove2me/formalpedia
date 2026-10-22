-- Prove2me | solution 1 for RetailInfoShare.AFS.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T13:53:15.266296+00:00
-- url     : https://prove2.me/submissions/12f2e518-823a-4eb1-a269-8912c533abc0

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

open RetailInfoShare.AFS RetailInfoShare.AFS.MeanAux in
theorem solution (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ)
    (M : NoiseMatrix P.N) (Q : Fin P.N → Ω → ℝ) (hQ : ∀ j, IsAdmissible Z M j (Q j)) :
    IsEquilibrium Z M Q ↔
      ∀ i, Q i =ᵐ[μ] fun ω =>
        (P.a - P.b * ∑ d ∈ Finset.univ.erase i, μ[Q d | info Z M i] ω
          + μ[Z.u | info Z M i] ω) / 2 := by
  haveI := Z.isProb
  have ha : 0 < 1 - P.alpha := by linarith [hP.2.2.2.2.2.2]
  have hL : ∀ d, MemLp (Q d) 2 μ := fun d => (hQ d).2
  -- the candidate best response of seller `i`
  let T : Fin P.N → Ω → ℝ := fun i ω =>
    (P.a - P.b * ∑ d ∈ Finset.univ.erase i, μ[Q d | info Z M i] ω
      + μ[Z.u | info Z M i] ω) / 2
  have hTm : ∀ i, StronglyMeasurable[info Z M i] (T i) := by
    intro i
    have h1 : StronglyMeasurable[info Z M i]
        (fun ω => ∑ d ∈ Finset.univ.erase i, μ[Q d | info Z M i] ω) :=
      Finset.stronglyMeasurable_fun_sum _ (fun d _ => stronglyMeasurable_condExp)
    have h2 : StronglyMeasurable[info Z M i] (fun ω =>
        P.a - P.b * ∑ d ∈ Finset.univ.erase i, μ[Q d | info Z M i] ω
          + μ[Z.u | info Z M i] ω) :=
      (stronglyMeasurable_const.sub (h1.const_mul P.b)).add stronglyMeasurable_condExp
    have e : T i = fun ω => (1 / 2 : ℝ) * (P.a - P.b * ∑ d ∈ Finset.univ.erase i,
        μ[Q d | info Z M i] ω + μ[Z.u | info Z M i] ω) := by
      funext ω; simp only [T]; ring
    rw [e]; exact h2.const_mul _
  have hTL : ∀ i, MemLp (T i) 2 μ := by
    intro i
    have h1 : MemLp (fun ω => ∑ d ∈ Finset.univ.erase i, μ[Q d | info Z M i] ω) 2 μ :=
      memLp_finsetSum _ (fun d _ => (hL d).condExp (by norm_num))
    have h2 : MemLp (fun ω =>
        P.a - P.b * ∑ d ∈ Finset.univ.erase i, μ[Q d | info Z M i] ω
          + μ[Z.u | info Z M i] ω) 2 μ :=
      ((memLp_const P.a).sub (h1.const_mul P.b)).add ((u_memLp Z).condExp (by norm_num))
    have e : T i = fun ω => (1 / 2 : ℝ) * (P.a - P.b * ∑ d ∈ Finset.univ.erase i,
        μ[Q d | info Z M i] ω + μ[Z.u | info Z M i] ω) := by
      funext ω; simp only [T]; ring
    rw [e]; exact h2.const_mul _
  have hT2 : ∀ i, (fun ω => 2 * T i ω) =ᵐ[μ] μ[resid Z Q i | info Z M i] := by
    intro i
    have hI : ∀ d, Integrable (Q d) μ := fun d => (hL d).integrable (by norm_num)
    have hS : Integrable (fun ω => ∑ d ∈ Finset.univ.erase i, Q d ω) μ :=
      integrable_finsetSum _ (fun d _ => hI d)
    have hu : Integrable Z.u μ := (u_memLp Z).integrable (by norm_num)
    have e : resid Z Q i = ((fun _ => P.a) - P.b • (∑ d ∈ Finset.univ.erase i, Q d)) + Z.u := by
      funext ω; simp [resid, Finset.sum_apply]
    have hS' : Integrable (∑ d ∈ Finset.univ.erase i, Q d) μ := by
      have : (∑ d ∈ Finset.univ.erase i, Q d) = fun ω => ∑ d ∈ Finset.univ.erase i, Q d ω := by
        funext ω; simp [Finset.sum_apply]
      rw [this]; exact hS
    rw [e]
    have c1 := condExp_add ((integrable_const P.a).sub (hS'.smul P.b)) hu (info Z M i) (μ := μ)
    have c2 := condExp_sub (integrable_const P.a) (hS'.smul P.b) (info Z M i) (μ := μ)
    have c3 := condExp_smul (μ := μ) P.b (∑ d ∈ Finset.univ.erase i, Q d) (info Z M i)
    have c4 := condExp_finsetSum (μ := μ) (s := Finset.univ.erase i) (fun d _ => hI d)
      (info Z M i)
    have c5 := condExp_const (μ := μ) (info_le Z M i) P.a
    filter_upwards [c1, c2, c3, c4] with ω h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.sub_apply, c5, h3, Pi.smul_apply, h4]
    simp only [T, Finset.sum_apply, smul_eq_mul]
    ring
  have hdec : ∀ i q, IsAdmissible Z M i q →
      sellerProfit Z (Function.update Q i q) i =
        (1 - P.alpha) * (∫ ω, T i ω ^ 2 ∂μ - ∫ ω, (q ω - T i ω) ^ 2 ∂μ) := by
    intro i q hq
    rw [sellerProfit_update]
    exact profit_decomp (info_le Z M i) P.alpha (resid Z Q i) (T i) q
      (resid_memLp Z Q hL i) (hT2 i) (hTL i) hq.1 hq.2
  have hself : ∀ i, Function.update Q i (Q i) = Q := fun i => by simp
  constructor
  · intro hE i
    have hle := hE.2 i (T i) ⟨hTm i, hTL i⟩
    rw [hdec i (T i) ⟨hTm i, hTL i⟩] at hle
    have h0 := hdec i (Q i) (hQ i)
    rw [hself i] at h0
    rw [h0] at hle
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      integral_zero, sub_zero] at hle
    have hint : Integrable (fun ω => (Q i ω - T i ω) ^ 2) μ :=
      ((hL i).sub (hTL i)).integrable_sq
    have hnn : 0 ≤ ∫ ω, (Q i ω - T i ω) ^ 2 ∂μ := integral_nonneg (fun ω => sq_nonneg _)
    have hz : ∫ ω, (Q i ω - T i ω) ^ 2 ∂μ = 0 := by nlinarith
    rw [integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hint] at hz
    filter_upwards [hz] with ω h
    have : (Q i ω - T i ω) ^ 2 = 0 := h
    have : Q i ω - T i ω = 0 := pow_eq_zero_iff (by norm_num) |>.mp this
    show Q i ω = T i ω
    linarith
  · intro hfoc
    refine ⟨hQ, fun j q hq => ?_⟩
    rw [hdec j q hq]
    have h0 := hdec j (Q j) (hQ j)
    rw [hself j] at h0
    rw [h0]
    have hz : ∫ ω, (Q j ω - T j ω) ^ 2 ∂μ = 0 := by
      have : (fun ω => (Q j ω - T j ω) ^ 2) =ᵐ[μ] fun _ => (0 : ℝ) := by
        filter_upwards [hfoc j] with ω h
        simp only [T]; rw [h]; ring
      rw [integral_congr_ae this]; simp
    rw [hz]
    have hnn : 0 ≤ ∫ ω, (q ω - T j ω) ^ 2 ∂μ := integral_nonneg (fun ω => sq_nonneg _)
    nlinarith
