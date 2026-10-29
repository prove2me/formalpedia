-- Prove2me | solution 1 for PGLandscape.FiniteHorizon.stationary_optimal_finite_horizon
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T22:10:10.613555+00:00
-- url     : https://prove2.me/submissions/e2f4ea73-d9bc-44ce-9b18-c3da30b591e6

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions
import Definitions.Def_PGLandscape_FiniteHorizon_Stages

set_option autoImplicit false

namespace P2M62d0

open MeasureTheory ProbabilityTheory PGLandscape.Closure PGLandscape.FiniteHorizon

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

theorem step_markov (M : MDP S A) (π : MPolicy S A) : IsMarkovKernel (stepKernel M π) := by
  unfold stepKernel; infer_instance

attribute [local instance] step_markov

theorem iter_markov (M : MDP S A) (π : MPolicy S A) (t : ℕ) :
    IsMarkovKernel (iterKernel M π t) := by
  induction t with
  | zero => simp only [iterKernel]; infer_instance
  | succ t ih => simp only [iterKernel]; infer_instance

attribute [local instance] iter_markov

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

theorem bind_prob (M : MDP S A) (π : MPolicy S A) (t : ℕ) :
    IsProbabilityMeasure (M.ρ.bind (iterKernel M π t)) := by
  show IsProbabilityMeasure (iterKernel M π t ∘ₘ M.ρ)
  infer_instance

attribute [local instance] bind_prob

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

theorem occ_prob (M : MDP S A) (π : MPolicy S A) : IsProbabilityMeasure (occupancy M π) :=
  ⟨occ_univ M π⟩

attribute [local instance] occ_prob

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
      gradient (lossParam M πθ) θ = gradient (piObjective M πθ θ) θ ∧
        DifferentiableAt ℝ (piObjective M πθ θ) θ := by
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
  refine ⟨h4'.differentiableAt, ?_, h5.differentiableAt⟩
  unfold gradient
  rw [h4'.fderiv, h5.fderiv]


/-! ### Finite-horizon part (Theorem 3) -/

lemma int_tau (μ : Measure S) [IsProbabilityMeasure μ] (τ : S) (hτm : MeasurableSet ({τ} : Set S))
    (hτ : μ {τ} = 1) {F : S → ℝ} (hF : Measurable F) : ∫ x, F x ∂μ = F τ := by
  have hc : μ ({τ} : Set S)ᶜ = 0 := (prob_compl_eq_zero_iff hτm).2 hτ
  have hae : ∀ᵐ x ∂μ, x ∈ ({τ} : Set S) := ae_iff.2 hc
  calc ∫ x, F x ∂μ = ∫ x, F x ∂(μ.restrict {τ}) := by
        rw [Measure.restrict_eq_self_of_ae_mem hae]
    _ = F τ := by
        rw [Measure.restrict_singleton, hτ, one_smul, integral_dirac' _ _ hF.stronglyMeasurable]

lemma tau_meas (stage : S → ℕ) (hm : Measurable stage) (H : ℕ) (τ : S)
    (hτ : ∀ s, stage s = H + 1 ↔ s = τ) : MeasurableSet ({τ} : Set S) := by
  have e : ({τ} : Set S) = stage ⁻¹' {H + 1} := by
    ext s; simp [hτ s]
  rw [e]; exact hm (measurableSet_singleton _)

lemma bp_tau (M : MDP S A) (τ : S) (hτm : MeasurableSet ({τ} : Set S))
    (habs : ∀ a, M.P (τ, a) {τ} = 1 ∧ M.g (τ, a) = 0) (a : S → A) {J : S → ℝ} (hJ : Measurable J) :
    bellmanPi M a J τ = M.γ * J τ := by
  unfold bellmanPi
  rw [(habs (a τ)).2, int_tau (M.P (τ, a τ)) τ hτm (habs (a τ)).1 hJ, zero_add]

lemma ctg_tau (M : MDP S A) (π : MPolicy S A) (τ : S) (hτm : MeasurableSet ({τ} : Set S))
    (habs : ∀ a, M.P (τ, a) {τ} = 1 ∧ M.g (τ, a) = 0) : costToGo M π τ = 0 := by
  have h := ctg_bellman M π τ
  rw [step_apply, (habs _).2, int_tau _ τ hτm (habs _).1 (ctg_meas M π), zero_add] at h
  have h1 := M.γ_lt_one
  have h2 : (1 - M.γ) * costToGo M π τ = 0 := by
    rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · linarith
  · exact h3

lemma bp_meas (M : MDP S A) (π : MPolicy S A) {J : S → ℝ} (hJ : Measurable J) :
    Measurable (bellmanPi M π.1 J) := by
  show Measurable fun s => M.g (s, π.1 s) + M.γ * ∫ s', J s' ∂(stepKernel M π s)
  exact (gpi_meas M π).add (measurable_const.mul (kint_meas (stepKernel M π) hJ))

lemma bp_bdd (M : MDP S A) (π : MPolicy S A) (Cg : ℝ) (hCg : ∀ p, |M.g p| ≤ Cg) {J : S → ℝ}
    (B : ℝ) (hB : ∀ s, |J s| ≤ B) (s : S) : |bellmanPi M π.1 J s| ≤ Cg + M.γ * B := by
  unfold bellmanPi
  have h1 := hCg (s, π.1 s)
  have h2 := abs_integral_le (M.P (s, π.1 s)) B hB
  have hγ := M.γ_pos
  calc |M.g (s, π.1 s) + M.γ * ∫ s', J s' ∂M.P (s, π.1 s)|
      ≤ |M.g (s, π.1 s)| + |M.γ * ∫ s', J s' ∂M.P (s, π.1 s)| := abs_add_le _ _
    _ ≤ Cg + M.γ * B := by
        rw [abs_mul, abs_of_pos hγ]
        exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 hγ.le)

lemma bp_int (M : MDP S A) (μ : Measure S) [IsProbabilityMeasure μ] (π : MPolicy S A)
    {J : S → ℝ} (hJ : Measurable J) (B : ℝ) (hB : ∀ s, |J s| ≤ B) :
    Integrable (bellmanPi M π.1 J) μ := by
  obtain ⟨Cg, hCg⟩ := M.g_bounded
  exact intg_of_bdd μ (bp_meas M π hJ) _ (bp_bdd M π Cg hCg B hB)

lemma obj_sub (M : MDP S A) (μ : Measure S) [IsProbabilityMeasure μ] (π π' : MPolicy S A)
    {J : S → ℝ} (hJ : Measurable J) (B : ℝ) (hB : ∀ s, |J s| ≤ B) :
    bellmanObj M π.1 μ J - bellmanObj M π'.1 μ J =
      ∫ s, (bellmanPi M π.1 J s - bellmanPi M π'.1 J s) ∂μ := by
  unfold bellmanObj
  rw [integral_sub (bp_int M μ π hJ B hB) (bp_int M μ π' hJ B hB)]

lemma bp_congr (M : MDP S A) {a b : S → A} {s : S} (h : a s = b s) (J : S → ℝ) :
    bellmanPi M a J s = bellmanPi M b J s := by
  unfold bellmanPi; rw [h]

/-- `J* ≤ T_π J*` for every feasible `π` (Bellman optimality, via Assumption 2). -/
lemma opt_bellman (M : MDP S A) (πstar : MPolicy S A) (hopt : IsOptimal M πstar)
    (hA2 : Assumption2 M) (π : MPolicy S A) (hπ : IsFeasible M π) (s : S) :
    costToGo M πstar s ≤ bellmanPi M π.1 (costToGo M πstar) s := by
  obtain ⟨Cg, hCg⟩ := M.g_bounded
  have hJm : Measurable (costToGo M πstar) := ctg_meas M πstar
  have hJb := ctg_bdd M πstar Cg hCg
  obtain ⟨πg, hgf, hg⟩ := hA2 (costToGo M πstar) hJm ⟨_, hJb⟩
  have hJgm := ctg_meas M πg
  have hJgb := ctg_bdd M πg Cg hCg
  obtain ⟨D, hD⟩ : ∃ D : S → ℝ, D = fun x => costToGo M πg x - costToGo M πstar x := ⟨_, rfl⟩
  have hDb : ∀ x, |D x| ≤ 2 * (Cg * (1 - M.γ)⁻¹) := fun x => by
    rw [hD]
    have a1 := abs_le.1 (hJgb x)
    have a2 := abs_le.1 (hJb x)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hDm : Measurable D := by rw [hD]; exact hJgm.sub hJm
  have key : ∀ x, D x ≤ M.γ * ∫ y, D y ∂(M.P (x, πg.1 x)) := by
    intro x
    have h1 := ctg_bellman M πg x
    have h2 := ctg_bellman M πstar x
    have h3 := hg x (πstar.1 x) (hopt.1 x)
    unfold bellmanPi at h3
    rw [step_apply] at h1 h2
    have h4 : ∫ y, D y ∂(M.P (x, πg.1 x)) = ∫ y, costToGo M πg y ∂(M.P (x, πg.1 x)) -
        ∫ y, costToGo M πstar y ∂(M.P (x, πg.1 x)) := by
      rw [hD]; exact integral_sub (intg_of_bdd _ hJgm _ hJgb) (intg_of_bdd _ hJm _ hJb)
    rw [h4, mul_sub, hD]
    show costToGo M πg x - costToGo M πstar x ≤ _
    linarith
  haveI : Nonempty S := ⟨s⟩
  have hbdd : BddAbove (Set.range D) :=
    ⟨2 * (Cg * (1 - M.γ)⁻¹), by rintro _ ⟨x, rfl⟩; exact (abs_le.1 (hDb x)).2⟩
  have hγ := M.γ_pos
  have hγ1 := M.γ_lt_one
  have hc : (⨆ x, D x) ≤ M.γ * ⨆ x, D x := by
    refine ciSup_le fun x => (key x).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hγ.le
    calc ∫ y, D y ∂(M.P (x, πg.1 x)) ≤ ∫ _y, (⨆ x, D x) ∂(M.P (x, πg.1 x)) :=
          integral_mono (intg_of_bdd _ hDm _ hDb) (integrable_const _) (fun y => le_ciSup hbdd y)
      _ = ⨆ x, D x := by simp
  have hc0 : (⨆ x, D x) ≤ 0 := by nlinarith
  have hJg_eq : costToGo M πg = costToGo M πstar := funext fun x => by
    refine le_antisymm ?_ (hopt.2 πg hgf x)
    have := (le_ciSup hbdd x).trans hc0
    rw [hD] at this
    simp only at this
    linarith
  have h5 : bellmanPi M πg.1 (costToGo M πstar) s = costToGo M πstar s := by
    have h1 := ctg_bellman M πg s
    rw [step_apply, hJg_eq] at h1
    unfold bellmanPi; exact h1.symm
  calc costToGo M πstar s = bellmanPi M πg.1 (costToGo M πstar) s := h5.symm
    _ ≤ bellmanPi M π.1 (costToGo M πstar) s := by
        have := hg s (π.1 s) (hπ s)
        unfold bellmanPi at this ⊢
        exact this

lemma star_fix (M : MDP S A) (πstar : MPolicy S A) (hopt : IsOptimal M πstar)
    (π' : MPolicy S A) (hπ' : IsOptimal M π') (s : S) :
    bellmanPi M π'.1 (costToGo M πstar) s = costToGo M πstar s := by
  have heq : costToGo M π' = costToGo M πstar :=
    funext fun x => le_antisymm (hπ'.2 πstar hopt.1 x) (hopt.2 π' hπ'.1 x)
  have h1 := ctg_bellman M π' s
  rw [step_apply, heq] at h1
  unfold bellmanPi; exact h1.symm

lemma occ_pos (M : MDP S A) (t : ℕ) : ENNReal.ofReal ((1 - M.γ) * M.γ ^ t) ≠ 0 := by
  have h0 := M.γ_pos
  have h1 := M.γ_lt_one
  exact (ENNReal.ofReal_pos.2 (mul_pos (by linarith) (pow_pos h0 t))).ne'

lemma occ_term_null (M : MDP S A) (π : MPolicy S A) (t : ℕ) {N : Set S}
    (h : occupancy M π N = 0) : M.ρ.bind (iterKernel M π t) N = 0 := by
  have hle := Measure.le_sum
    (fun t : ℕ => ENNReal.ofReal ((1 - M.γ) * M.γ ^ t) • M.ρ.bind (iterKernel M π t)) t
  have h2 : (ENNReal.ofReal ((1 - M.γ) * M.γ ^ t) • M.ρ.bind (iterKernel M π t)) N = 0 :=
    le_antisymm ((Measure.le_iff'.1 hle N).trans h.le) (by positivity)
  rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero] at h2
  exact h2.resolve_left (occ_pos M t)

lemma rho_ac (M : MDP S A) (π : MPolicy S A) : M.ρ ≪ occupancy M π := by
  intro N hN
  have h3 := occ_term_null M π 0 hN
  have hk : M.ρ.bind (iterKernel M π 0) = M.ρ := by
    have e : (⇑(iterKernel M π 0) : S → Measure S) = fun s => Measure.dirac s := by
      funext s; show (Kernel.id : Kernel S S) s = _; rw [Kernel.id_apply]
    rw [e]; exact Measure.bind_dirac
  rwa [hk] at h3

lemma null_step (M : MDP S A) (π : MPolicy S A) (hac : occupancy M π ≪ M.ρ) {N : Set S}
    (hN : MeasurableSet N) (h0 : M.ρ N = 0) : ∀ᵐ s ∂M.ρ, M.P (s, π.1 s) N = 0 := by
  have h3 := occ_term_null M π 1 (hac h0)
  have hk : iterKernel M π 1 = stepKernel M π := by
    show stepKernel M π ∘ₖ iterKernel M π 0 = _
    show stepKernel M π ∘ₖ Kernel.id = _
    exact Kernel.comp_id _
  rw [hk, Measure.bind_apply hN (Kernel.aemeasurable _),
    lintegral_eq_zero_iff (Kernel.measurable_coe _ hN)] at h3
  filter_upwards [h3] with s hs
  exact hs

lemma dterm (M : MDP S A) (stage : S → ℕ) (hsm : Measurable stage) (H : ℕ)
    (hstep : ∀ s, stage s ≤ H → ∀ a ∈ M.As s, M.P (s, a) {s' | stage s' = stage s + 1} = 1)
    (h : ℕ) (hh : h ≤ H) (π : MPolicy S A) (hπf : IsFeasible M π) (hac : occupancy M π ≪ M.ρ)
    {D : S → ℝ} (hDm : Measurable D) (hIH : ∀ᵐ s ∂M.ρ, h + 1 ≤ stage s → D s = 0) :
    ∀ᵐ s ∂M.ρ, stage s = h → ∫ y, D y ∂(M.P (s, π.1 s)) = 0 := by
  have hNm : MeasurableSet {s | h + 1 ≤ stage s ∧ D s ≠ 0} :=
    (hsm (MeasurableSet.of_discrete (s := {n : ℕ | h + 1 ≤ n}))).inter
      (hDm (measurableSet_singleton (0 : ℝ))).compl
  have hN0 : M.ρ {s | h + 1 ≤ stage s ∧ D s ≠ 0} = 0 :=
    measure_mono_null (fun s hs => by
      simp only [Set.mem_setOf_eq] at hs ⊢
      exact fun hc => hs.2 (hc hs.1)) (ae_iff.1 hIH :
        M.ρ {s | ¬ (h + 1 ≤ stage s → D s = 0)} = 0)
  have hP := null_step M π hac hNm hN0
  filter_upwards [hP] with s hs hstage
  have hle : stage s ≤ H := hstage ▸ hh
  have hone : M.P (s, π.1 s) {s' | stage s' = stage s + 1} = 1 := hstep s hle (π.1 s) (hπf s)
  apply integral_eq_zero_of_ae
  have hm : MeasurableSet {y | stage y = stage s + 1} :=
    hsm (MeasurableSet.of_discrete (s := {n : ℕ | n = stage s + 1}))
  have hA : ∀ᵐ y ∂(M.P (s, π.1 s)), stage y = stage s + 1 :=
    ae_iff.2 ((prob_compl_eq_zero_iff hm).2 hone)
  have hB : ∀ᵐ y ∂(M.P (s, π.1 s)), y ∉ {s | h + 1 ≤ stage s ∧ D s ≠ 0} := by
    rw [ae_iff]; simp only [not_not, Set.setOf_mem_eq]; exact hs
  filter_upwards [hA, hB] with y hy1 hy2
  show D y = 0
  by_contra hne
  exact hy2 ⟨by omega, hne⟩

lemma bs_apply {d : ℕ} (blk : Fin d → ℕ) (h : ℕ) (a b : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    blockSwap blk h a b i = if blk i = h then a i else b i := rfl

lemma deriv_compare {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (F G : E → ℝ) (x z u v : E) (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G z)
    (h : ∀ t ∈ Set.Ioo (0 : ℝ) 1, G (z + t • u) - G z ≤ F (x + t • v) - F x) :
    inner ℝ u (gradient G z) ≤ inner ℝ v (gradient F x) := by
  have e : ∀ (K : E → ℝ) (p w : E), inner ℝ w (gradient K p) = fderiv ℝ K p w := by
    intro K p w
    rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply]
  have hd : ∀ (K : E → ℝ) (p w : E), DifferentiableAt ℝ K p →
      HasDerivAt (fun t : ℝ => K (p + t • w)) (fderiv ℝ K p w) 0 := by
    intro K p w hK
    have h2 : HasDerivAt (fun t : ℝ => p + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add p
    have hl : HasFDerivAt K (fderiv ℝ K p) (p + (0 : ℝ) • w) := by
      simpa using hK.hasFDerivAt
    exact hl.comp_hasDerivAt (0 : ℝ) h2
  have l1 := (hd F x v hF).tendsto_slope_zero_right
  have l2 := (hd G z u hG).tendsto_slope_zero_right
  rw [e F x v, e G z u]
  refine le_of_tendsto_of_tendsto l2 l1 ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (h t ht) (inv_nonneg.2 ht.1.le)

set_option maxHeartbeats 1000000 in
theorem main (M : MDP S A) (πstar : MPolicy S A) (hopt : IsOptimal M πstar)
    (hA2 : Assumption2 M) {d : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (πθ : EuclideanSpace ℝ (Fin d) → MPolicy S A) (hΘ : IsPolicyClass M Θ πθ)
    (H : ℕ) (stage : S → ℕ) (τ : S) (blk : Fin d → ℕ)
    (hC0 : Condition0 M Θ πθ) (hC3 : Condition3 M H stage τ blk Θ πθ)
    (hC4 : Condition4 M Θ πθ πstar) (hA3 : Assumption3 M Θ πθ)
    (hcontains : ∃ θstar ∈ Θ, IsOptimal M (πθ θstar)) (θ : EuclideanSpace ℝ (Fin d))
    (hst : IsStationary (lossParam M πθ) Θ θ) :
    loss M (πθ θ) = loss M πstar := by
  obtain ⟨Cg, hCg⟩ := M.g_bounded
  obtain ⟨θs, hθs, hθsopt⟩ := hcontains
  obtain ⟨hθ, -, hstat⟩ := hst
  obtain ⟨hstaged, -, hswap, hC5⟩ := hC3
  obtain ⟨hsm, hsr, hstep, hτiff, hτabs⟩ := hstaged
  have hτm : MeasurableSet ({τ} : Set S) := tau_meas stage hsm H τ hτiff
  have hfeas : ∀ y ∈ Θ, IsFeasible M (πθ y) := hΘ.2
  have hJsm : Measurable (costToGo M πstar) := ctg_meas M πstar
  have hJsb := ctg_bdd M πstar Cg hCg
  have hJtm : Measurable (costToGo M (πθ θ)) := ctg_meas M (πθ θ)
  have hJtb := ctg_bdd M (πθ θ) Cg hCg
  have hTs : ∀ y ∈ Θ, ∀ s, costToGo M πstar s ≤ bellmanPi M (πθ y).1 (costToGo M πstar) s :=
    fun y hy s => opt_bellman M πstar hopt hA2 (πθ y) (hfeas y hy) s
  have hfix : ∀ s, bellmanPi M (πθ θs).1 (costToGo M πstar) s = costToGo M πstar s :=
    star_fix M πstar hopt (πθ θs) hθsopt
  have hbpτ : ∀ (a : S → A) {J : S → ℝ}, Measurable J → bellmanPi M a J τ = M.γ * J τ :=
    fun a J hJ => bp_tau M τ hτm hτabs a hJ
  have hpol : ∀ y z : EuclideanSpace ℝ (Fin d), ∀ s, stage s ≤ H →
      (∀ i, blk i = stage s → y i = z i) → ∀ J : S → ℝ,
        bellmanPi M (πθ y).1 J s = bellmanPi M (πθ z).1 J s :=
    fun y z s hs hi J => bp_congr M (hC5 y z s hs hi) J
  have hcases : ∀ s, stage s ≤ H ∨ s = τ := by
    intro s
    rcases Nat.lt_or_ge (stage s) (H + 1) with h1 | h1
    · left; omega
    · right; exact (hτiff s).1 (le_antisymm (hsr s).2 h1)
  -- gradient of the loss
  obtain ⟨U, hU, hθU, hF⟩ := hC0 θ hθ
  obtain ⟨-, hgr, hdf⟩ := grad_eq M πθ θ U hU hθU hF
  have hfstat : ∀ z ∈ Θ, 0 ≤ inner ℝ (z - θ) (gradient (piObjective M πθ θ) θ) := by
    intro z hz; rw [← hgr]; exact hstat z hz
  obtain ⟨D, hD⟩ : ∃ D : S → ℝ, D = fun s => costToGo M (πθ θ) s - costToGo M πstar s :=
    ⟨_, rfl⟩
  have hDm : Measurable D := by rw [hD]; exact hJtm.sub hJsm
  have hdt : ∀ h, h ≤ H → (∀ᵐ s ∂M.ρ, h + 1 ≤ stage s → D s = 0) → ∀ y ∈ Θ,
      ∀ᵐ s ∂M.ρ, stage s = h → bellmanPi M (πθ y).1 (costToGo M (πθ θ)) s =
        bellmanPi M (πθ y).1 (costToGo M πstar) s := by
    intro h hh hIH y hy
    filter_upwards [dterm M stage hsm H hstep h hh (πθ y) (hfeas y hy) (hA3 y hy) hDm hIH]
      with s hs hstage
    have h0 := hs hstage
    simp only [hD] at h0
    rw [integral_sub (intg_of_bdd _ hJtm _ hJtb) (intg_of_bdd _ hJsm _ hJsb)] at h0
    unfold bellmanPi
    rw [sub_eq_zero.1 h0]
  have hstepP : ∀ h, 1 ≤ h → h ≤ H → (∀ᵐ s ∂M.ρ, h + 1 ≤ stage s → D s = 0) →
      (∀ᵐ s ∂M.ρ, h ≤ stage s → D s = 0) := by
    intro h h1 hH hIH
    have hx : blockSwap blk h θ θs ∈ Θ := hswap θs hθs θ hθ h
    have hdtθ := hdt h hH hIH
    -- the mixed point is stationary for B(· | η_θ, J*)
    have hgx : IsStationary (fun θbar => bellmanObj M (πθ θbar).1 (occupancy M (πθ θ))
        (costToGo M πstar)) Θ (blockSwap blk h θ θs) := by
      refine ⟨hx, (hC4 θ hθ).1 _ hx, fun x' hx' => ?_⟩
      have hz : blockSwap blk h x' θ ∈ Θ := hswap θ hθ x' hx' h
      have key : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
          piObjective M πθ θ (θ + t • (blockSwap blk h x' θ - θ)) - piObjective M πθ θ θ ≤
          bellmanObj M (πθ (blockSwap blk h θ θs + t • (x' - blockSwap blk h θ θs))).1
              (occupancy M (πθ θ)) (costToGo M πstar) -
            bellmanObj M (πθ (blockSwap blk h θ θs)).1 (occupancy M (πθ θ)) (costToGo M πstar) := by
        intro t ht
        have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
        have hy : blockSwap blk h θ θs + t • (x' - blockSwap blk h θ θs) ∈ Θ :=
          hΘ.1.add_smul_sub_mem hx hx' htI
        have hw : θ + t • (blockSwap blk h x' θ - θ) ∈ Θ := hΘ.1.add_smul_sub_mem hθ hz htI
        unfold piObjective
        rw [obj_sub M _ _ _ hJtm _ hJtb, obj_sub M _ _ _ hJsm _ hJsb]
        refine integral_mono_ae ((bp_int M _ _ hJtm _ hJtb).sub (bp_int M _ _ hJtm _ hJtb))
          ((bp_int M _ _ hJsm _ hJsb).sub (bp_int M _ _ hJsm _ hJsb)) ?_
        filter_upwards [(hA3 θ hθ).ae_le (hdtθ _ hw), (hA3 θ hθ).ae_le (hdtθ θ hθ)]
          with s hs1 hs2
        rcases hcases s with hsH | hsτ
        · by_cases hsh : stage s = h
          · rw [hs1 hsh, hs2 hsh]
            have e1 := hpol (θ + t • (blockSwap blk h x' θ - θ))
              (blockSwap blk h θ θs + t • (x' - blockSwap blk h θ θs)) s hsH (fun i hi => by
                simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, bs_apply, smul_eq_mul,
                  hi, hsh, if_true]) (costToGo M πstar)
            have e2 := hpol θ (blockSwap blk h θ θs) s hsH (fun i hi => by
                simp only [bs_apply, hi, hsh, if_true]) (costToGo M πstar)
            rw [e1, e2]
          · have e1 := hpol (θ + t • (blockSwap blk h x' θ - θ)) θ s hsH (fun i hi => by
                have : blk i ≠ h := hi ▸ hsh
                simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, bs_apply, smul_eq_mul,
                  this, if_false, sub_self, mul_zero, add_zero]) (costToGo M (πθ θ))
            have e2 := hpol (blockSwap blk h θ θs) θs s hsH (fun i hi => by
                have : blk i ≠ h := hi ▸ hsh
                simp only [bs_apply, this, if_false]) (costToGo M πstar)
            rw [e1, e2, hfix s, sub_self, sub_nonneg]
            exact hTs _ hy s
        · subst hsτ
          rw [hbpτ _ hJtm, hbpτ _ hJtm, hbpτ _ hJsm, hbpτ _ hJsm]
          simp
      have hcmp := deriv_compare
        (fun θbar => bellmanObj M (πθ θbar).1 (occupancy M (πθ θ)) (costToGo M πstar))
        (piObjective M πθ θ) (blockSwap blk h θ θs) θ (blockSwap blk h x' θ - θ)
        (x' - blockSwap blk h θ θs) ((hC4 θ hθ).1 _ hx) hdf key
      have := hfstat _ hz
      linarith
    have hle := (hC4 θ hθ).2 _ hgx θs hθs
    have hle' : bellmanObj M (πθ (blockSwap blk h θ θs)).1 (occupancy M (πθ θ)) (costToGo M πstar) -
        bellmanObj M (πθ θs).1 (occupancy M (πθ θ)) (costToGo M πstar) ≤ 0 := by linarith
    rw [obj_sub M _ _ _ hJsm _ hJsb] at hle'
    have hnn : 0 ≤ fun s => bellmanPi M (πθ (blockSwap blk h θ θs)).1 (costToGo M πstar) s -
        bellmanPi M (πθ θs).1 (costToGo M πstar) s := by
      intro s
      simp only [Pi.zero_apply]
      rcases hcases s with hsH | hsτ
      · by_cases hsh : stage s = h
        · have e2 := hpol θ (blockSwap blk h θ θs) s hsH (fun i hi => by
              simp only [bs_apply, hi, hsh, if_true]) (costToGo M πstar)
          rw [← e2, hfix s, sub_nonneg]
          exact hTs θ hθ s
        · have e2 := hpol (blockSwap blk h θ θs) θs s hsH (fun i hi => by
              have : blk i ≠ h := hi ▸ hsh
              simp only [bs_apply, this, if_false]) (costToGo M πstar)
          rw [e2, sub_self]
      · subst hsτ
        rw [hbpτ _ hJsm, hbpτ _ hJsm, sub_self]
    have hint := (bp_int M (occupancy M (πθ θ)) (πθ (blockSwap blk h θ θs)) hJsm _ hJsb).sub
      (bp_int M (occupancy M (πθ θ)) (πθ θs) hJsm _ hJsb)
    have hz0 := (integral_eq_zero_iff_of_nonneg hnn hint).1
      (le_antisymm hle' (integral_nonneg hnn))
    have hz0' := (rho_ac M (πθ θ)).ae_le hz0
    filter_upwards [hIH, hdtθ θ hθ, hz0'] with s hs1 hs2 hs3 hs
    rcases Nat.eq_or_lt_of_le hs with hsh | hsh
    · have hsh' : stage s = h := hsh.symm
      have hsH : stage s ≤ H := by omega
      have e2 := hpol θ (blockSwap blk h θ θs) s hsH (fun i hi => by
          simp only [bs_apply, hi, hsh', if_true]) (costToGo M πstar)
      simp only [Pi.zero_apply] at hs3
      rw [hfix s, ← e2] at hs3
      have hb := ctg_bellman M (πθ θ) s
      rw [step_apply] at hb
      have h2 := hs2 hsh'
      unfold bellmanPi at h2
      rw [hD]
      show costToGo M (πθ θ) s - costToGo M πstar s = 0
      have h3 : bellmanPi M (πθ θ).1 (costToGo M πstar) s = costToGo M πstar s := by linarith
      unfold bellmanPi at h3
      linarith
    · exact hs1 hsh
  have hbase : ∀ᵐ s ∂M.ρ, H + 1 ≤ stage s → D s = 0 := Filter.Eventually.of_forall fun s hs => by
    have h1 : stage s = H + 1 := le_antisymm (hsr s).2 hs
    rw [hτiff] at h1
    rw [h1, hD]
    simp only [ctg_tau M _ τ hτm hτabs, sub_self]
  have hall : ∀ k, k ≤ H → ∀ᵐ s ∂M.ρ, H + 1 - k ≤ stage s → D s = 0 := by
    intro k
    induction k with
    | zero => intro _; simpa using hbase
    | succ k ih =>
      intro hk
      have e : H - k + 1 = H + 1 - k := by omega
      have := hstepP (H - k) (by omega) (by omega) (by rw [e]; exact ih (by omega))
      have e2 : H + 1 - (k + 1) = H - k := by omega
      rw [e2]; exact this
  have hfin : ∀ᵐ s ∂M.ρ, D s = 0 := by
    filter_upwards [hall H le_rfl] with s hs
    exact hs (by have := (hsr s).1; omega)
  unfold loss
  congr 1
  apply integral_congr_ae
  filter_upwards [hfin] with s hs
  rw [hD] at hs
  simp only at hs
  linarith

end P2M62d0

open PGLandscape.FiniteHorizon MeasureTheory ProbabilityTheory in
theorem solution {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (M : PGLandscape.Closure.MDP S A) (πstar : PGLandscape.Closure.MPolicy S A) (hopt : PGLandscape.Closure.IsOptimal M πstar)
    (hA1 : PGLandscape.Closure.Assumption1 M πstar) (hA2 : PGLandscape.Closure.Assumption2 M)
    {d : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (πθ : EuclideanSpace ℝ (Fin d) → PGLandscape.Closure.MPolicy S A) (hΘ : PGLandscape.Closure.IsPolicyClass M Θ πθ)
    (H : ℕ) (stage : S → ℕ) (τ : S) (blk : Fin d → ℕ)
    (hC0 : PGLandscape.Closure.Condition0 M Θ πθ) (hC3 : Condition3 M H stage τ blk Θ πθ)
    (hC4 : Condition4 M Θ πθ πstar) (hA3 : Assumption3 M Θ πθ)
    (hcontains : ∃ θstar ∈ Θ, PGLandscape.Closure.IsOptimal M (πθ θstar)) :
    ∀ θ : EuclideanSpace ℝ (Fin d), PGLandscape.Closure.IsStationary (PGLandscape.Closure.lossParam M πθ) Θ θ →
      PGLandscape.Closure.loss M (πθ θ) = PGLandscape.Closure.loss M πstar := by
  intro θ hθ
  exact P2M62d0.main M πstar hopt hA2 Θ πθ hΘ H stage τ blk hC0 hC3 hC4 hA3 hcontains θ hθ
