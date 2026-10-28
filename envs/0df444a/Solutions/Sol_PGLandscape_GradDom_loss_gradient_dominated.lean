-- Prove2me | solution 1 for PGLandscape.GradDom.loss_gradient_dominated
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T09:01:37.861974+00:00
-- url     : https://prove2.me/submissions/07bc920c-6f5d-43d8-bba6-0881873f4c5e

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions

set_option autoImplicit false

namespace P2MEdac

open MeasureTheory ProbabilityTheory PGLandscape.Closure

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

instance step_markov (M : MDP S A) (π : MPolicy S A) : IsMarkovKernel (stepKernel M π) := by
  unfold stepKernel; infer_instance

instance iter_markov (M : MDP S A) (π : MPolicy S A) (t : ℕ) :
    IsMarkovKernel (iterKernel M π t) := by
  induction t with
  | zero => simp only [iterKernel]; infer_instance
  | succ t ih => simp only [iterKernel]; infer_instance

lemma step_apply (M : MDP S A) (π : MPolicy S A) (s : S) :
    stepKernel M π s = M.P (s, π.1 s) := rfl

lemma iter_succ' (M : MDP S A) (π : MPolicy S A) (t : ℕ) :
    iterKernel M π (t + 1) = iterKernel M π t ∘ₖ stepKernel M π := by
  induction t with
  | zero => simp [iterKernel]
  | succ t ih =>
    show stepKernel M π ∘ₖ iterKernel M π (t + 1) = iterKernel M π (t + 1) ∘ₖ stepKernel M π
    conv_lhs => rw [ih]
    rw [← Kernel.comp_assoc]
    rfl

lemma intg_of_bdd {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {h : X → ℝ} (hm : Measurable h) (K : ℝ) (hK : ∀ x, |h x| ≤ K) : Integrable h μ :=
  Integrable.of_bound hm.aestronglyMeasurable K (Filter.Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using hK x)

lemma abs_integral_le {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {h : X → ℝ} (K : ℝ) (hK : ∀ x, |h x| ≤ K) : |∫ x, h x ∂μ| ≤ K := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := h) (C := K)
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hK x)
  simpa [Real.norm_eq_abs] using this

lemma gpi_meas (M : MDP S A) (π : MPolicy S A) : Measurable fun s => M.g (s, π.1 s) :=
  M.g_measurable.comp (measurable_id.prodMk π.2)

lemma kint_meas {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (κ : Kernel X Y)
    {h : Y → ℝ} (hm : Measurable h) : Measurable fun x => ∫ y, h y ∂κ x :=
  (hm.stronglyMeasurable.integral_kernel (κ := κ)).measurable

/-- the per-step expected cost `h_t(s) = ∫ g_π d(P^t_s)` -/
noncomputable def hfun (M : MDP S A) (π : MPolicy S A) (t : ℕ) (s : S) : ℝ :=
  ∫ s', M.g (s', π.1 s') ∂(iterKernel M π t s)

lemma hfun_meas (M : MDP S A) (π : MPolicy S A) (t : ℕ) : Measurable (hfun M π t) :=
  kint_meas _ (gpi_meas M π)

lemma hfun_bdd (M : MDP S A) (π : MPolicy S A) (Cg : ℝ) (hCg : ∀ p, |M.g p| ≤ Cg) (t : ℕ)
    (s : S) : |hfun M π t s| ≤ Cg :=
  abs_integral_le _ Cg (fun _ => hCg _)

lemma term_bdd (M : MDP S A) (π : MPolicy S A) (Cg : ℝ) (hCg : ∀ p, |M.g p| ≤ Cg) (t : ℕ)
    (s : S) : ‖M.γ ^ t * hfun M π t s‖ ≤ Cg * M.γ ^ t := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg M.γ_pos.le t), mul_comm]
  exact mul_le_mul_of_nonneg_right (hfun_bdd M π Cg hCg t s) (pow_nonneg M.γ_pos.le t)

lemma geom_sum (M : MDP S A) (Cg : ℝ) :
    HasSum (fun t : ℕ => Cg * M.γ ^ t) (Cg * (1 - M.γ)⁻¹) :=
  (hasSum_geometric_of_lt_one M.γ_pos.le M.γ_lt_one).mul_left Cg

lemma term_summable (M : MDP S A) (π : MPolicy S A) (Cg : ℝ) (hCg : ∀ p, |M.g p| ≤ Cg)
    (s : S) : Summable fun t => M.γ ^ t * hfun M π t s :=
  (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (term_bdd M π Cg hCg · s)
    (geom_sum M Cg).summable).of_norm

lemma ctg_eq (M : MDP S A) (π : MPolicy S A) (s : S) :
    costToGo M π s = ∑' t, M.γ ^ t * hfun M π t s := rfl

lemma ctg_meas (M : MDP S A) (π : MPolicy S A) : Measurable (costToGo M π) := by
  obtain ⟨Cg, hCg⟩ := M.g_bounded
  refine measurable_of_tendsto_metrizable
    (f := fun n s => ∑ t ∈ Finset.range n, M.γ ^ t * hfun M π t s)
    (fun n => Finset.measurable_sum _ fun t _ => measurable_const.mul (hfun_meas M π t)) ?_
  rw [tendsto_pi_nhds]
  intro s
  exact (term_summable M π Cg hCg s).hasSum.tendsto_sum_nat

lemma ctg_bdd (M : MDP S A) (π : MPolicy S A) (Cg : ℝ) (hCg : ∀ p, |M.g p| ≤ Cg) (s : S) :
    |costToGo M π s| ≤ Cg * (1 - M.γ)⁻¹ := by
  rw [← Real.norm_eq_abs, ctg_eq]
  exact tsum_of_norm_bounded (geom_sum M Cg) (term_bdd M π Cg hCg · s)

/-- Bellman equation for the cost-to-go of a policy. -/
lemma ctg_bellman (M : MDP S A) (π : MPolicy S A) (s : S) :
    costToGo M π s = M.g (s, π.1 s) + M.γ * ∫ s', costToGo M π s' ∂(stepKernel M π s) := by
  obtain ⟨Cg, hCg⟩ := M.g_bounded
  have hγ := M.γ_pos
  rw [ctg_eq, (term_summable M π Cg hCg s).tsum_eq_zero_add]
  congr 1
  · simp [hfun, iterKernel, Kernel.id_apply, integral_dirac' _ _ (gpi_meas M π).stronglyMeasurable]
  · have h1 : ∀ t, M.γ ^ (t + 1) * hfun M π (t + 1) s
        = M.γ * ∫ s', M.γ ^ t * hfun M π t s' ∂(stepKernel M π s) := by
      intro t
      rw [hfun, iter_succ', Kernel.integral_comp, integral_const_mul]
      · simp only [hfun]; ring
      · exact intg_of_bdd _ (gpi_meas M π) Cg (fun _ => hCg _)
    simp_rw [h1]
    rw [tsum_mul_left]
    congr 1
    simp_rw [ctg_eq]
    refine integral_tsum_of_summable_integral_norm
      (fun t => intg_of_bdd _ (measurable_const.mul (hfun_meas M π t)) _
        (fun x => by simpa [Real.norm_eq_abs] using term_bdd M π Cg hCg t x)) ?_
    refine Summable.of_nonneg_of_le (fun t => integral_nonneg fun _ => norm_nonneg _)
      (fun t => ?_) (geom_sum M Cg).summable
    have := abs_integral_le (stepKernel M π s) (h := fun x => ‖M.γ ^ t * hfun M π t x‖)
      (Cg * M.γ ^ t) (fun x => by rw [abs_of_nonneg (norm_nonneg _)]; exact term_bdd M π Cg hCg t x)
    exact (le_abs_self _).trans this

instance bind_prob (M : MDP S A) (π : MPolicy S A) (t : ℕ) :
    IsProbabilityMeasure (M.ρ.bind (iterKernel M π t)) := by
  show IsProbabilityMeasure (iterKernel M π t ∘ₘ M.ρ)
  infer_instance

lemma int_bind (μ : Measure S) [IsProbabilityMeasure μ] (κ : Kernel S S) [IsMarkovKernel κ]
    {f : S → ℝ} (hm : Measurable f) (K : ℝ) (hK : ∀ x, |f x| ≤ K) :
    ∫ x, f x ∂(μ.bind κ) = ∫ s, ∫ x, f x ∂(κ s) ∂μ := by
  show ∫ x, f x ∂(κ ∘ₘ μ) = _
  rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp (intg_of_bdd _ hm K hK)]
  simp only [Kernel.const_apply]

lemma int_succ (M : MDP S A) (π : MPolicy S A) (t : ℕ) {f : S → ℝ} (hm : Measurable f) (K : ℝ)
    (hK : ∀ x, |f x| ≤ K) :
    ∫ x, f x ∂(M.ρ.bind (iterKernel M π (t + 1))) =
      ∫ s, (∫ x, f x ∂(stepKernel M π s)) ∂(M.ρ.bind (iterKernel M π t)) := by
  rw [int_bind _ _ hm K hK, int_bind _ _ (kint_meas _ hm) K (fun s => abs_integral_le _ K hK)]
  congr 1
  funext s
  show ∫ x, f x ∂((stepKernel M π ∘ₖ iterKernel M π t) s) = _
  rw [Kernel.integral_comp (intg_of_bdd _ hm K hK)]

lemma int_zero (M : MDP S A) (π : MPolicy S A) {f : S → ℝ} (hm : Measurable f) (K : ℝ)
    (hK : ∀ x, |f x| ≤ K) :
    ∫ x, f x ∂(M.ρ.bind (iterKernel M π 0)) = ∫ x, f x ∂M.ρ := by
  rw [int_bind _ _ hm K hK]
  congr 1
  funext s
  show ∫ x, f x ∂(Kernel.id s) = f s
  rw [Kernel.id_apply, integral_dirac' _ _ hm.stronglyMeasurable]

lemma occ_univ (M : MDP S A) (π : MPolicy S A) : occupancy M π Set.univ = 1 := by
  have hγ0 := M.γ_pos
  have hγ1 := M.γ_lt_one
  simp only [occupancy, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => mul_nonneg (by linarith) (pow_nonneg hγ0.le t))
    ((summable_geometric_of_lt_one hγ0.le hγ1).mul_left _), tsum_mul_left,
    tsum_geometric_of_lt_one hγ0.le hγ1, mul_inv_cancel₀ (by linarith), ENNReal.ofReal_one]

instance occ_prob (M : MDP S A) (π : MPolicy S A) : IsProbabilityMeasure (occupancy M π) :=
  ⟨occ_univ M π⟩

lemma summ_g (M : MDP S A) (u : ℕ → ℝ) (K : ℝ) (hu : ∀ t, |u t| ≤ K) :
    Summable fun t => M.γ ^ t * u t := by
  have h : ∀ t, ‖M.γ ^ t * u t‖ ≤ K * M.γ ^ t := by
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg M.γ_pos.le t), mul_comm]
    exact mul_le_mul_of_nonneg_right (hu t) (pow_nonneg M.γ_pos.le t)
  exact (Summable.of_nonneg_of_le (fun t => norm_nonneg (M.γ ^ t * u t)) h
    (geom_sum M K).summable).of_norm

lemma occ_int (M : MDP S A) (π : MPolicy S A) {f : S → ℝ} (hm : Measurable f) (K : ℝ)
    (hK : ∀ x, |f x| ≤ K) :
    ∫ x, f x ∂(occupancy M π) =
      ∑' t, (1 - M.γ) * M.γ ^ t * ∫ x, f x ∂(M.ρ.bind (iterKernel M π t)) := by
  have hγ0 := M.γ_pos
  have hγ1 := M.γ_lt_one
  have hi := intg_of_bdd (occupancy M π) hm K hK
  unfold occupancy at hi ⊢
  rw [integral_sum_measure hi]
  refine tsum_congr fun t => ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal (mul_nonneg (by linarith) (pow_nonneg hγ0.le t)),
    smul_eq_mul]

lemma occ_ge (M : MDP S A) (π : MPolicy S A) {f : S → ℝ} (hm : Measurable f) (K : ℝ)
    (hK : ∀ x, |f x| ≤ K) (h0 : ∀ s, 0 ≤ f s) :
    (1 - M.γ) * ∫ x, f x ∂M.ρ ≤ ∫ x, f x ∂(occupancy M π) := by
  have hγ0 := M.γ_pos
  have hγ1 := M.γ_lt_one
  rw [occ_int M π hm K hK]
  have hs : Summable fun t => (1 - M.γ) * M.γ ^ t * ∫ x, f x ∂(M.ρ.bind (iterKernel M π t)) := by
    have := (summ_g M _ K (fun t => abs_integral_le (M.ρ.bind (iterKernel M π t)) K hK)).mul_left
      (1 - M.γ)
    simpa only [mul_assoc] using this
  have := hs.le_tsum 0 (fun t _ => mul_nonneg (mul_nonneg (by linarith) (pow_nonneg hγ0.le t))
    (integral_nonneg h0))
  rw [int_zero M π hm K hK, pow_zero, mul_one] at this
  exact this

/-- Performance difference identity. -/
lemma pdl (M : MDP S A) (π π' : MPolicy S A) :
    loss M π' - loss M π = bellmanObj M π'.1 (occupancy M π') (costToGo M π)
      - bellmanObj M π.1 (occupancy M π') (costToGo M π) := by
  obtain ⟨Cg, hCg⟩ := M.g_bounded
  have hγ0 := M.γ_pos
  have hγ1 := M.γ_lt_one
  have hJm : Measurable (costToGo M π) := ctg_meas M π
  have hJb : ∀ s, |costToGo M π s| ≤ Cg * (1 - M.γ)⁻¹ := ctg_bdd M π Cg hCg
  have hgm := gpi_meas M π'
  have hgb : ∀ s, |M.g (s, π'.1 s)| ≤ Cg := fun s => hCg _
  let a : ℕ → ℝ := fun t => ∫ x, costToGo M π x ∂(M.ρ.bind (iterKernel M π' t))
  let b : ℕ → ℝ := fun t => ∫ x, M.g (x, π'.1 x) ∂(M.ρ.bind (iterKernel M π' t))
  have ha : ∀ t, |a t| ≤ Cg * (1 - M.γ)⁻¹ := fun t => abs_integral_le _ _ hJb
  have hb : ∀ t, |b t| ≤ Cg := fun t => abs_integral_le _ Cg hgb
  have e1 : bellmanObj M π.1 (occupancy M π') (costToGo M π) =
      ∫ x, costToGo M π x ∂(occupancy M π') := by
    unfold bellmanObj
    congr 1
    funext s
    exact (ctg_bellman M π s).symm
  have e2 : ∫ x, costToGo M π x ∂(occupancy M π') = ∑' t, (1 - M.γ) * M.γ ^ t * a t :=
    occ_int M π' hJm _ hJb
  have hPm : Measurable fun x => ∫ y, costToGo M π y ∂(stepKernel M π' x) := kint_meas _ hJm
  have hPb : ∀ x, |∫ y, costToGo M π y ∂(stepKernel M π' x)| ≤ Cg * (1 - M.γ)⁻¹ :=
    fun x => abs_integral_le _ _ hJb
  have hTm : Measurable (bellmanPi M π'.1 (costToGo M π)) := hgm.add (measurable_const.mul hPm)
  have hTb : ∀ s, |bellmanPi M π'.1 (costToGo M π) s| ≤ Cg + M.γ * (Cg * (1 - M.γ)⁻¹) := by
    intro s
    have h1 := abs_le.1 (hPb s)
    have h2 := abs_le.1 (hgb s)
    show |M.g (s, π'.1 s) + M.γ * ∫ y, costToGo M π y ∂(stepKernel M π' s)| ≤ _
    rw [abs_le]
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  have e3 : bellmanObj M π'.1 (occupancy M π') (costToGo M π) =
      ∑' t, (1 - M.γ) * M.γ ^ t * (b t + M.γ * a (t + 1)) := by
    unfold bellmanObj
    rw [occ_int M π' hTm _ hTb]
    refine tsum_congr fun t => ?_
    congr 1
    show ∫ x, (M.g (x, π'.1 x) + M.γ * ∫ y, costToGo M π y ∂(stepKernel M π' x))
      ∂(M.ρ.bind (iterKernel M π' t)) = _
    rw [integral_add (intg_of_bdd _ hgm Cg hgb) ((intg_of_bdd _ hPm _ hPb).const_mul _),
      integral_const_mul]
    congr 2
    exact (int_succ M π' t hJm _ hJb).symm
  have e4 : ∫ s, costToGo M π' s ∂M.ρ = ∑' t, M.γ ^ t * b t := by
    have hint : ∀ t, Integrable (fun s => M.γ ^ t * hfun M π' t s) M.ρ := fun t =>
      intg_of_bdd _ (measurable_const.mul (hfun_meas M π' t)) _
        (fun x => by simpa [Real.norm_eq_abs] using term_bdd M π' Cg hCg t x)
    simp_rw [ctg_eq]
    rw [← integral_tsum_of_summable_integral_norm hint ?_]
    · refine tsum_congr fun t => ?_
      rw [integral_const_mul]
      congr 1
      exact (int_bind M.ρ (iterKernel M π' t) hgm Cg hgb).symm
    · refine Summable.of_nonneg_of_le (fun t => integral_nonneg fun _ => norm_nonneg _)
        (fun t => ?_) (geom_sum M Cg).summable
      have := abs_integral_le M.ρ (h := fun x => ‖M.γ ^ t * hfun M π' t x‖)
        (Cg * M.γ ^ t) (fun x => by
          rw [abs_of_nonneg (norm_nonneg _)]; exact term_bdd M π' Cg hCg t x)
      exact (le_abs_self _).trans this
  have e5 : ∫ s, costToGo M π s ∂M.ρ = a 0 := (int_zero M π' hJm _ hJb).symm
  have sa : Summable fun t => M.γ ^ t * a t := summ_g M a _ ha
  have sa1 : Summable fun t => M.γ ^ t * a (t + 1) := summ_g M _ _ (fun t => ha (t + 1))
  have sb : Summable fun t => M.γ ^ t * b t := summ_g M b Cg hb
  have f1 : ∑' t, (1 - M.γ) * M.γ ^ t * (b t + M.γ * a (t + 1)) =
      (1 - M.γ) * ∑' t, M.γ ^ t * b t + (1 - M.γ) * M.γ * ∑' t, M.γ ^ t * a (t + 1) := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add (sb.mul_left _) (sa1.mul_left _)]
    exact tsum_congr fun t => by ring
  have s2 : Summable fun t => (1 - M.γ) * M.γ ^ t * a t := by
    have := sa.mul_left (1 - M.γ)
    simpa only [mul_assoc] using this
  have f2 : ∑' t, (1 - M.γ) * M.γ ^ t * a t =
      (1 - M.γ) * a 0 + (1 - M.γ) * M.γ * ∑' t, M.γ ^ t * a (t + 1) := by
    rw [s2.tsum_eq_zero_add, ← tsum_mul_left]
    congr 1
    · simp
    · exact tsum_congr fun t => by ring
  unfold loss
  rw [e3, e1, e2, e4, e5, f1, f2]
  ring

lemma grad_eq {d : ℕ} (M : MDP S A) (πθ : EuclideanSpace ℝ (Fin d) → MPolicy S A)
    (θ : EuclideanSpace ℝ (Fin d))
    (U : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) (hU : IsOpen U)
    (hθU : (θ, θ) ∈ U)
    (hF : ContDiffOn ℝ 1
      (fun p => bellmanObj M (πθ p.1).1 (occupancy M (πθ p.2)) (costToGo M (πθ θ))) U) :
    DifferentiableAt ℝ (lossParam M πθ) θ ∧
      gradient (lossParam M πθ) θ = gradient (piObjective M πθ θ) θ := by
  set F := fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
    bellmanObj M (πθ p.1).1 (occupancy M (πθ p.2)) (costToGo M (πθ θ)) with hFdef
  have hd : DifferentiableAt ℝ F (θ, θ) :=
    (hF.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hθU)
  have hL := hd.hasFDerivAt
  have h1 := HasFDerivAt.comp (f := fun x : EuclideanSpace ℝ (Fin d) => (x, x)) θ hL
    ((hasFDerivAt_id θ).prodMk (hasFDerivAt_id θ))
  have h2 := HasFDerivAt.comp (f := fun x : EuclideanSpace ℝ (Fin d) => (θ, x)) θ hL
    ((hasFDerivAt_const θ θ).prodMk (hasFDerivAt_id θ))
  have h3 := HasFDerivAt.comp (f := fun x : EuclideanSpace ℝ (Fin d) => (x, θ)) θ hL
    ((hasFDerivAt_id θ).prodMk (hasFDerivAt_const θ θ))
  have hloss : lossParam M πθ = fun x => loss M (πθ θ) + (F (x, x) - F (θ, x)) := by
    funext x
    have := pdl M (πθ θ) (πθ x)
    show loss M (πθ x) = _
    simp only [hFdef]
    linarith
  have h4 := (h1.sub h2).const_add (loss M (πθ θ))
  have hEq : ((fderiv ℝ F (θ, θ)).comp ((ContinuousLinearMap.id ℝ _).prod (ContinuousLinearMap.id ℝ _)) -
      (fderiv ℝ F (θ, θ)).comp ((0 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)).prod
        (ContinuousLinearMap.id ℝ _))) =
      (fderiv ℝ F (θ, θ)).comp ((ContinuousLinearMap.id ℝ _).prod
        (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))) := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply]
    rw [← map_sub]
    congr 1
    ext <;> simp
  have h4' : HasFDerivAt (lossParam M πθ) ((fderiv ℝ F (θ, θ)).comp ((ContinuousLinearMap.id ℝ _).prod
        (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))) θ := by
    rw [hloss, ← hEq]; exact h4
  have h5 : HasFDerivAt (piObjective M πθ θ) ((fderiv ℝ F (θ, θ)).comp ((ContinuousLinearMap.id ℝ _).prod
        (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))) θ := h3
  refine ⟨h4'.differentiableAt, ?_⟩
  unfold gradient
  rw [h4'.fderiv, h5.fderiv]

end P2MEdac

open MeasureTheory ProbabilityTheory in
theorem solution {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : PGLandscape.Closure.MDP S A)
    (πstar : PGLandscape.Closure.MPolicy S A) (hopt : PGLandscape.Closure.IsOptimal M πstar) (hA1 : PGLandscape.Closure.Assumption1 M πstar)
    (hA2 : PGLandscape.Closure.Assumption2 M)
    {d : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d))) (πθ : EuclideanSpace ℝ (Fin d) → PGLandscape.Closure.MPolicy S A)
    (hΘ : PGLandscape.Closure.IsPolicyClass M Θ πθ)
    (c μ : ℝ) (hc : 0 < c) (hμ : 0 ≤ μ) (κ : ℝ) (hκ : 0 < κ) (hκb : PGLandscape.Closure.IsConcBound M Θ πθ πstar κ)
    (hC0 : PGLandscape.Closure.Condition0 M Θ πθ) (hC1 : PGLandscape.Closure.Condition1 M Θ πθ) (hC2B : PGLandscape.Closure.Condition2B M Θ πθ c μ) :
    PGLandscape.Closure.IsGradDominated (PGLandscape.Closure.lossParam M πθ) Θ (κ / (1 - M.γ) * c) (κ / (1 - M.γ) * μ) := by
  obtain ⟨Cg, hCg⟩ := M.g_bounded
  have hγ0 := M.γ_pos
  have hγ1 := M.γ_lt_one
  have h1γ : 0 < 1 - M.γ := by linarith
  have hK : 0 < κ / (1 - M.γ) := div_pos hκ h1γ
  refine ⟨mul_pos hK hc, mul_nonneg hK.le hμ, fun θ hθ => ?_⟩
  obtain ⟨U, hU, hθU, hF⟩ := hC0 θ hθ
  obtain ⟨hdiff, hgrad⟩ := P2MEdac.grad_eq M πθ θ U hU hθU hF
  refine ⟨hdiff, fun y hy m hm => ?_⟩
  have hJm := P2MEdac.ctg_meas M (πθ θ)
  have hJb := P2MEdac.ctg_bdd M (πθ θ) Cg hCg
  have hJsm := P2MEdac.ctg_meas M πstar
  have hJsb := P2MEdac.ctg_bdd M πstar Cg hCg
  have hJym := P2MEdac.ctg_meas M (πθ y)
  have hJyb := P2MEdac.ctg_bdd M (πθ y) Cg hCg
  obtain ⟨πg, hgf, hgr⟩ := hA2 (PGLandscape.Closure.costToGo M (πθ θ)) hJm ⟨_, hJb⟩
  have hbdd : ∀ s, BddBelow (Set.range fun a : M.As s =>
      M.g (s, a.1) + M.γ * ∫ s', PGLandscape.Closure.costToGo M (πθ θ) s' ∂(M.P (s, a.1))) := by
    intro s
    exact ⟨PGLandscape.Closure.bellmanPi M πg.1 (PGLandscape.Closure.costToGo M (πθ θ)) s,
      by rintro _ ⟨a, rfl⟩; exact hgr s a.1 a.2⟩
  have hT : ∀ s, PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M (πθ θ)) s =
      PGLandscape.Closure.bellmanPi M πg.1 (PGLandscape.Closure.costToGo M (πθ θ)) s := by
    intro s
    have : Nonempty (M.As s) := (M.As_nonempty s).to_subtype
    apply le_antisymm
    · exact ciInf_le (hbdd s) ⟨πg.1 s, hgf s⟩
    · exact le_ciInf fun a => hgr s a.1 a.2
  have hTJ : ∀ s, PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M (πθ θ)) s ≤
      PGLandscape.Closure.costToGo M (πθ θ) s := fun s =>
    (ciInf_le (hbdd s) ⟨(πθ θ).1 s, hΘ.2 θ hθ s⟩).trans
      (le_of_eq (P2MEdac.ctg_bellman M (πθ θ) s).symm)
  have hPm : Measurable fun x =>
      ∫ y, PGLandscape.Closure.costToGo M (πθ θ) y ∂(PGLandscape.Closure.stepKernel M πg x) :=
    P2MEdac.kint_meas _ hJm
  have hTm : Measurable (PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M (πθ θ))) := by
    have e : PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M (πθ θ)) =
        PGLandscape.Closure.bellmanPi M πg.1 (PGLandscape.Closure.costToGo M (πθ θ)) := funext hT
    rw [e]
    exact (P2MEdac.gpi_meas M πg).add (measurable_const.mul hPm)
  have hTb : ∀ s, |PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M (πθ θ)) s| ≤
      Cg + M.γ * (Cg * (1 - M.γ)⁻¹) := by
    intro s
    rw [hT]
    have h1 := abs_le.1 (P2MEdac.abs_integral_le (M.P (s, πg.1 s)) _ hJb)
    have h2 := abs_le.1 (hCg (s, πg.1 s))
    unfold PGLandscape.Closure.bellmanPi
    rw [abs_le]
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  -- D = J - TJ ≥ 0
  have hDm : Measurable fun s => PGLandscape.Closure.costToGo M (πθ θ) s -
      PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M (πθ θ)) s := hJm.sub hTm
  have hDb : ∀ s, |PGLandscape.Closure.costToGo M (πθ θ) s -
      PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M (πθ θ)) s| ≤
      Cg * (1 - M.γ)⁻¹ + (Cg + M.γ * (Cg * (1 - M.γ)⁻¹)) := by
    intro s
    have h1 := abs_le.1 (hJb s)
    have h2 := abs_le.1 (hTb s)
    rw [abs_le]
    constructor <;> linarith
  have hD0 : ∀ s, 0 ≤ PGLandscape.Closure.costToGo M (πθ θ) s -
      PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M (πθ θ)) s :=
    fun s => sub_nonneg.2 (hTJ s)
  -- the occupancy-weighted gap
  have hiJη := P2MEdac.intg_of_bdd (PGLandscape.Closure.occupancy M (πθ θ)) hJm _ hJb
  have hiTη := P2MEdac.intg_of_bdd (PGLandscape.Closure.occupancy M (πθ θ)) hTm _ hTb
  have hDη : ∫ s, (PGLandscape.Closure.costToGo M (πθ θ) s -
      PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M (πθ θ)) s)
        ∂(PGLandscape.Closure.occupancy M (πθ θ)) =
      ∫ s, PGLandscape.Closure.costToGo M (πθ θ) s ∂(PGLandscape.Closure.occupancy M (πθ θ)) -
      ∫ s, PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M (πθ θ)) s
        ∂(PGLandscape.Closure.occupancy M (πθ θ)) := integral_sub hiJη hiTη
  have hBθ : PGLandscape.Closure.piObjective M πθ θ θ =
      ∫ s, PGLandscape.Closure.costToGo M (πθ θ) s ∂(PGLandscape.Closure.occupancy M (πθ θ)) := by
    unfold PGLandscape.Closure.piObjective PGLandscape.Closure.bellmanObj
    congr 1
    funext s
    exact (P2MEdac.ctg_bellman M (πθ θ) s).symm
  have hBg : PGLandscape.Closure.bellmanObj M πg.1 (PGLandscape.Closure.occupancy M (πθ θ))
      (PGLandscape.Closure.costToGo M (πθ θ)) =
      ∫ s, PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M (πθ θ)) s
        ∂(PGLandscape.Closure.occupancy M (πθ θ)) := by
    unfold PGLandscape.Closure.bellmanObj
    congr 1
    funext s
    exact (hT s).symm
  obtain ⟨θp, hθp, hp⟩ := hC1 θ hθ
  have hp' := hp πg hgf
  obtain ⟨_, _, hGD⟩ := hC2B θ hθ
  have hm' : ∀ x' ∈ Θ, m / (κ / (1 - M.γ)) ≤
      c * inner ℝ (gradient (PGLandscape.Closure.piObjective M πθ θ) θ) (x' - θ) +
        μ / 2 * ‖θ - x'‖ ^ 2 := by
    intro x' hx'
    have h := hm x' hx'
    rw [hgrad] at h
    rw [div_le_iff₀ hK]
    calc m ≤ _ := h
      _ = _ := by ring
  have hB := (hGD θ hθ).2 θp hθp _ hm'
  -- the ρ-weighted gap
  have hocc := P2MEdac.occ_ge M (πθ θ) hDm _ hDb hD0
  have hconc := hκb θ hθ
  have e1 : (fun s => |PGLandscape.Closure.costToGo M (πθ θ) s - PGLandscape.Closure.costToGo M πstar s|) =
      fun s => PGLandscape.Closure.costToGo M (πθ θ) s - PGLandscape.Closure.costToGo M πstar s :=
    funext fun s => abs_of_nonneg (sub_nonneg.2 (hopt.2 (πθ θ) (hΘ.2 θ hθ) s))
  have e2 : (fun s => |PGLandscape.Closure.costToGo M (πθ θ) s -
      PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M (πθ θ)) s|) =
      fun s => PGLandscape.Closure.costToGo M (πθ θ) s -
      PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M (πθ θ)) s :=
    funext fun s => abs_of_nonneg (hD0 s)
  rw [e1, e2] at hconc
  have hiJ := P2MEdac.intg_of_bdd M.ρ hJm _ hJb
  have hiJs := P2MEdac.intg_of_bdd M.ρ hJsm _ hJsb
  have hiJy := P2MEdac.intg_of_bdd M.ρ hJym _ hJyb
  rw [integral_sub hiJ hiJs] at hconc
  have hstar : PGLandscape.Closure.loss M πstar ≤ PGLandscape.Closure.loss M (πθ y) := by
    unfold PGLandscape.Closure.loss
    exact mul_le_mul_of_nonneg_left
      (integral_mono hiJs hiJy fun s => hopt.2 (πθ y) (hΘ.2 y hy) s) h1γ.le
  show PGLandscape.Closure.loss M (πθ θ) + m ≤ PGLandscape.Closure.loss M (πθ y)
  have hlθ : PGLandscape.Closure.loss M (πθ θ) - PGLandscape.Closure.loss M πstar =
      (1 - M.γ) * (∫ s, PGLandscape.Closure.costToGo M (πθ θ) s ∂M.ρ -
        ∫ s, PGLandscape.Closure.costToGo M πstar s ∂M.ρ) := by
    unfold PGLandscape.Closure.loss; ring
  set K := κ / (1 - M.γ) with hKdef
  set Iρ := ∫ s, (PGLandscape.Closure.costToGo M (πθ θ) s -
      PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M (πθ θ)) s) ∂M.ρ
  set Iη := ∫ s, (PGLandscape.Closure.costToGo M (πθ θ) s -
      PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M (πθ θ)) s)
        ∂(PGLandscape.Closure.occupancy M (πθ θ))
  have hIη : Iη ≤ -(m / K) := by
    rw [hDη]; rw [hBθ] at hB; linarith
  have s1 := mul_le_mul_of_nonneg_left hconc h1γ.le
  have s2 : (1 - M.γ) * (K * Iρ) = K * ((1 - M.γ) * Iρ) := by ring
  have s3 := mul_le_mul_of_nonneg_left hocc hK.le
  have s4 := mul_le_mul_of_nonneg_left hIη hK.le
  have s5 : K * (-(m / K)) = -m := by field_simp
  linarith
