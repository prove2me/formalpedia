-- Prove2me | solution 1 for PGLandscape.Concentrability.conc_le_density_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T12:32:00.260582+00:00
-- url     : https://prove2.me/submissions/445fb995-3a37-402f-b7bb-05cc85fecd36

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions

set_option autoImplicit false

namespace P2M2bcf

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

lemma bind_lintegral (M : MDP S A) (π : MPolicy S A) (t : ℕ) {h : S → ENNReal}
    (hm : Measurable h) :
    ∫⁻ s, h s ∂(M.ρ.bind (iterKernel M π t)) = ∫⁻ s, ∫⁻ x, h x ∂(iterKernel M π t s) ∂M.ρ :=
  Measure.lintegral_bind (Kernel.aemeasurable _) hm.aemeasurable

lemma occ_lintegral (M : MDP S A) (π : MPolicy S A) (h : S → ENNReal) :
    ∫⁻ s, h s ∂(occupancy M π) =
      ∑' t, ENNReal.ofReal ((1 - M.γ) * M.γ ^ t) * ∫⁻ s, h s ∂(M.ρ.bind (iterKernel M π t)) := by
  simp only [occupancy, lintegral_sum_measure, lintegral_smul_measure, smul_eq_mul]

lemma key (M : MDP S A) (π : MPolicy S A) (C : ℝ)
    (hC : ∀ B, MeasurableSet B → occupancy M π B ≤ ENNReal.ofReal C * M.ρ B)
    {D f : S → ℝ} (hDm : Measurable D) (hfm : Measurable f) (KD : ℝ) (hDb : ∀ s, |D s| ≤ KD)
    (hD0 : ∀ s, 0 ≤ D s) (hf0 : ∀ s, 0 ≤ f s) (Kf : ℝ) (hfb : ∀ s, |f s| ≤ Kf)
    (hle : ∀ s, D s ≤ f s + M.γ * ∫ x, D x ∂(stepKernel M π s)) :
    ∫ s, D s ∂M.ρ ≤ C / (1 - M.γ) * ∫ s, f s ∂M.ρ := by
  have hγ0 := M.γ_pos
  have hγ1 := M.γ_lt_one
  let Dn : S → ENNReal := fun s => ENNReal.ofReal (D s)
  let fn : S → ENNReal := fun s => ENNReal.ofReal (f s)
  have hDnm : Measurable Dn := ENNReal.measurable_ofReal.comp hDm
  have hfnm : Measurable fn := ENNReal.measurable_ofReal.comp hfm
  let γe : ENNReal := ENNReal.ofReal M.γ
  have h1 : ∀ s, Dn s ≤ fn s + γe * ∫⁻ x, Dn x ∂(stepKernel M π s) := by
    intro s
    have hi : Integrable D (stepKernel M π s) := intg_of_bdd _ hDm KD hDb
    have e : ∫⁻ x, Dn x ∂(stepKernel M π s) = ENNReal.ofReal (∫ x, D x ∂(stepKernel M π s)) :=
      (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hD0)).symm
    rw [e, ← ENNReal.ofReal_mul hγ0.le,
      ← ENNReal.ofReal_add (hf0 s) (mul_nonneg hγ0.le (integral_nonneg hD0))]
    exact ENNReal.ofReal_le_ofReal (hle s)
  let μ : ℕ → Measure S := fun t => M.ρ.bind (iterKernel M π t)
  have hbind : ∀ t (h : S → ENNReal), Measurable h →
      ∫⁻ s, h s ∂(μ t) = ∫⁻ s, ∫⁻ x, h x ∂(iterKernel M π t s) ∂M.ρ :=
    fun t h hm => bind_lintegral M π t hm
  let a : ℕ → ENNReal := fun t => ∫⁻ s, Dn s ∂(μ t)
  let b : ℕ → ENNReal := fun t => ∫⁻ s, fn s ∂(μ t)
  have h2 : ∀ t, a t ≤ b t + γe * a (t + 1) := by
    intro t
    have e : a (t + 1) = ∫⁻ s, (∫⁻ x, Dn x ∂(stepKernel M π s)) ∂(μ t) := by
      show ∫⁻ s, Dn s ∂(μ (t + 1)) = _
      rw [hbind (t + 1) _ hDnm, hbind t _ hDnm.lintegral_kernel]
      congr 1
      funext s
      show ∫⁻ x, Dn x ∂((stepKernel M π ∘ₖ iterKernel M π t) s) = _
      rw [Kernel.lintegral_comp _ _ _ hDnm]
    rw [e]
    calc a t ≤ ∫⁻ s, (fn s + γe * ∫⁻ x, Dn x ∂(stepKernel M π s)) ∂(μ t) :=
          lintegral_mono fun s => h1 s
      _ = _ := by rw [lintegral_add_left hfnm, lintegral_const_mul _ hDnm.lintegral_kernel]
  have hconst : ∀ t (c : ENNReal), ∫⁻ _s, c ∂(μ t) = c := by
    intro t c
    rw [hbind t _ measurable_const]
    simp [lintegral_const, measure_univ]
  have ha_le : ∀ t, a t ≤ ENNReal.ofReal KD := by
    intro t
    calc a t ≤ ∫⁻ _s, ENNReal.ofReal KD ∂(μ t) :=
          lintegral_mono fun s => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hDb s))
      _ = _ := hconst t _
  let c : ℕ → ENNReal := fun t => ENNReal.ofReal ((1 - M.γ) * M.γ ^ t)
  have hc_succ : ∀ t, c (t + 1) = γe * c t := by
    intro t
    show ENNReal.ofReal ((1 - M.γ) * M.γ ^ (t + 1)) = ENNReal.ofReal M.γ * ENNReal.ofReal ((1 - M.γ) * M.γ ^ t)
    rw [← ENNReal.ofReal_mul hγ0.le]
    congr 1
    ring
  have hcsum : ∑' t, c t ≠ ⊤ := by
    show ∑' t, ENNReal.ofReal ((1 - M.γ) * M.γ ^ t) ≠ ⊤
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => mul_nonneg (by linarith) (pow_nonneg hγ0.le t))
      ((summable_geometric_of_lt_one hγ0.le hγ1).mul_left _)]
    exact ENNReal.ofReal_ne_top
  have hη : ∀ h : S → ENNReal, ∫⁻ s, h s ∂(occupancy M π) = ∑' t, c t * ∫⁻ s, h s ∂(μ t) :=
    fun h => occ_lintegral M π h
  let X : ENNReal := ∑' t, γe * (c t * a (t + 1))
  have hX : X ≠ ⊤ := by
    have hle' : X ≤ ∑' t, γe * (c t * ENNReal.ofReal KD) :=
      ENNReal.tsum_le_tsum fun t => by gcongr; exact ha_le _
    refine ne_top_of_le_ne_top ?_ hle'
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hcsum ENNReal.ofReal_ne_top)
  have hsum : c 0 * a 0 + X ≤ ∫⁻ s, fn s ∂(occupancy M π) + X := by
    have eL : ∑' t, c t * a t = c 0 * a 0 + X := by
      rw [tsum_eq_zero_add' ENNReal.summable]
      congr 1
      refine tsum_congr fun t => ?_
      rw [hc_succ]
      ring
    have hlt : ∑' t, c t * a t ≤ ∑' t, c t * b t + X := by
      rw [← ENNReal.tsum_add]
      refine ENNReal.tsum_le_tsum fun t => ?_
      calc c t * a t ≤ c t * (b t + γe * a (t + 1)) := by gcongr; exact h2 t
        _ = _ := by ring
    rw [hη fn, ← eL]
    exact hlt
  have hmain : c 0 * a 0 ≤ ∫⁻ s, fn s ∂(occupancy M π) := ENNReal.le_of_add_le_add_right hX hsum
  have hle_meas : occupancy M π ≤ ENNReal.ofReal C • M.ρ := by
    rw [Measure.le_iff]
    intro B hB
    simpa using hC B hB
  have hF : ∫⁻ s, fn s ∂(occupancy M π) ≤ ENNReal.ofReal C * ∫⁻ s, fn s ∂M.ρ := by
    calc _ ≤ ∫⁻ s, fn s ∂(ENNReal.ofReal C • M.ρ) := lintegral_mono' hle_meas le_rfl
      _ = _ := by rw [lintegral_smul_measure]; rfl
  have ha0 : a 0 = ∫⁻ s, Dn s ∂M.ρ := by
    show ∫⁻ s, Dn s ∂(μ 0) = _
    rw [hbind 0 _ hDnm]
    congr 1
    funext s
    show ∫⁻ x, Dn x ∂(Kernel.id s) = _
    rw [Kernel.id_apply, lintegral_dirac' _ hDnm]
  have e0 : c 0 = ENNReal.ofReal (1 - M.γ) := by
    show ENNReal.ofReal ((1 - M.γ) * M.γ ^ 0) = _
    rw [pow_zero, mul_one]
  have hCpos : 1 - M.γ ≤ C := by
    have h := hC Set.univ MeasurableSet.univ
    have e : occupancy M π Set.univ = ∑' t, c t := by
      rw [← lintegral_one, hη (fun _ => 1)]
      refine tsum_congr fun t => ?_
      rw [hconst t 1, mul_one]
    have h' : c 0 ≤ ENNReal.ofReal C := by
      calc c 0 ≤ ∑' t, c t := ENNReal.le_tsum 0
        _ = _ := e.symm
        _ ≤ _ := by simpa using h
    rw [e0] at h'
    rcases ENNReal.ofReal_le_ofReal_iff'.1 h' with h'' | h''
    · exact h''
    · linarith
  have hfin : ENNReal.ofReal (1 - M.γ) * ∫⁻ s, Dn s ∂M.ρ ≤ ENNReal.ofReal C * ∫⁻ s, fn s ∂M.ρ := by
    rw [← e0, ← ha0]
    exact hmain.trans hF
  have hIntD : ∫ s, D s ∂M.ρ = (∫⁻ s, Dn s ∂M.ρ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hD0) hDm.aestronglyMeasurable
  have hIntf : ∫ s, f s ∂M.ρ = (∫⁻ s, fn s ∂M.ρ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfm.aestronglyMeasurable
  have hfnfin : ∫⁻ s, fn s ∂M.ρ ≠ ⊤ := by
    have hb' : ∫⁻ s, fn s ∂M.ρ ≤ ∫⁻ _s, ENNReal.ofReal Kf ∂M.ρ :=
      lintegral_mono fun s => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hfb s))
    refine ne_top_of_le_ne_top ?_ hb'
    simp
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfnfin) hfin
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal (by linarith), ← hIntD, ← hIntf] at hreal
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  linarith

end P2M2bcf

open PGLandscape.Closure MeasureTheory ProbabilityTheory in
theorem solution {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : PGLandscape.Closure.MDP S A)
    (πstar : PGLandscape.Closure.MPolicy S A) (hopt : PGLandscape.Closure.IsOptimal M πstar) (hA1 : PGLandscape.Closure.Assumption1 M πstar)
    (hA2 : PGLandscape.Closure.Assumption2 M)
    {d : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d))) (πθ : EuclideanSpace ℝ (Fin d) → PGLandscape.Closure.MPolicy S A)
    (hΘ : PGLandscape.Closure.IsPolicyClass M Θ πθ)
    (C : ℝ) (hC : ∀ B, MeasurableSet B → PGLandscape.Closure.occupancy M πstar B ≤ ENNReal.ofReal C * M.ρ B) :
    PGLandscape.Closure.IsConcBound M Θ πθ πstar C := by
  intro θ hθ
  obtain ⟨Cg, hCg⟩ := M.g_bounded
  have hγ0 := M.γ_pos
  have hJm := P2M2bcf.ctg_meas M (πθ θ)
  have hJsm := P2M2bcf.ctg_meas M πstar
  have hJb := P2M2bcf.ctg_bdd M (πθ θ) Cg hCg
  have hJsb := P2M2bcf.ctg_bdd M πstar Cg hCg
  obtain ⟨πg, hgf, hgr⟩ := hA2 (costToGo M (πθ θ)) hJm ⟨_, hJb⟩
  have hbdd : ∀ s, BddBelow (Set.range fun a : M.As s =>
      M.g (s, a.1) + M.γ * ∫ s', costToGo M (πθ θ) s' ∂(M.P (s, a.1))) := by
    intro s
    exact ⟨bellmanPi M πg.1 (costToGo M (πθ θ)) s, by rintro _ ⟨a, rfl⟩; exact hgr s a.1 a.2⟩
  have hT : ∀ s, bellmanOpt M (costToGo M (πθ θ)) s = bellmanPi M πg.1 (costToGo M (πθ θ)) s := by
    intro s
    have : Nonempty (M.As s) := (M.As_nonempty s).to_subtype
    apply le_antisymm
    · exact ciInf_le (hbdd s) ⟨πg.1 s, hgf s⟩
    · exact le_ciInf fun a => hgr s a.1 a.2
  have hTle : ∀ s, bellmanOpt M (costToGo M (πθ θ)) s ≤
      M.g (s, πstar.1 s) + M.γ * ∫ s', costToGo M (πθ θ) s' ∂(stepKernel M πstar s) := by
    intro s
    exact ciInf_le (hbdd s) ⟨πstar.1 s, hopt.1 s⟩
  have hfeq : (fun s => |costToGo M (πθ θ) s - bellmanOpt M (costToGo M (πθ θ)) s|) =
      fun s => |costToGo M (πθ θ) s - (M.g (s, πg.1 s) +
        M.γ * ∫ x, costToGo M (πθ θ) x ∂(stepKernel M πg s))| := by
    funext s
    rw [hT]
    rfl
  have hfm : Measurable (fun s => |costToGo M (πθ θ) s - bellmanOpt M (costToGo M (πθ θ)) s|) := by
    rw [hfeq]
    exact continuous_abs.measurable.comp (hJm.sub ((P2M2bcf.gpi_meas M πg).add
      (measurable_const.mul (P2M2bcf.kint_meas _ hJm))))
  have hfb : ∀ s, |(|costToGo M (πθ θ) s - bellmanOpt M (costToGo M (πθ θ)) s|)| ≤
      Cg * (1 - M.γ)⁻¹ + (Cg + M.γ * (Cg * (1 - M.γ)⁻¹)) := by
    intro s
    rw [abs_abs, hT]
    have h1 := abs_le.1 (hJb s)
    have h3 := abs_le.1 (P2M2bcf.abs_integral_le (M.P (s, πg.1 s)) _ hJb)
    have h4 := abs_le.1 (hCg (s, πg.1 s))
    unfold bellmanPi
    rw [abs_le]
    constructor <;> nlinarith [h1.1, h1.2, h3.1, h3.2, h4.1, h4.2]
  have hD0 : ∀ s, 0 ≤ costToGo M (πθ θ) s - costToGo M πstar s :=
    fun s => sub_nonneg.2 (hopt.2 (πθ θ) (hΘ.2 θ hθ) s)
  have hDb : ∀ s, |costToGo M (πθ θ) s - costToGo M πstar s| ≤
      Cg * (1 - M.γ)⁻¹ + Cg * (1 - M.γ)⁻¹ := by
    intro s
    have h1 := abs_le.1 (hJb s)
    have h2 := abs_le.1 (hJsb s)
    rw [abs_le]
    constructor <;> linarith
  have hDle : ∀ s, costToGo M (πθ θ) s - costToGo M πstar s ≤
      |costToGo M (πθ θ) s - bellmanOpt M (costToGo M (πθ θ)) s| +
        M.γ * ∫ x, (costToGo M (πθ θ) x - costToGo M πstar x) ∂(stepKernel M πstar s) := by
    intro s
    have hb := P2M2bcf.ctg_bellman M πstar s
    have hi1 := P2M2bcf.intg_of_bdd (stepKernel M πstar s) hJm _ hJb
    have hi2 := P2M2bcf.intg_of_bdd (stepKernel M πstar s) hJsm _ hJsb
    rw [integral_sub hi1 hi2]
    have h5 := hTle s
    have h6 := le_abs_self (costToGo M (πθ θ) s - bellmanOpt M (costToGo M (πθ θ)) s)
    nlinarith [h5, h6, hb]
  have hkey := P2M2bcf.key M πstar C hC (hJm.sub hJsm) hfm _ hDb hD0
    (fun s => abs_nonneg _) _ hfb hDle
  have e1 : (fun s => |costToGo M (πθ θ) s - costToGo M πstar s|) =
      fun s => costToGo M (πθ θ) s - costToGo M πstar s :=
    funext fun s => abs_of_nonneg (hD0 s)
  show ∫ s, |costToGo M (πθ θ) s - costToGo M πstar s| ∂M.ρ ≤ _
  rw [e1]
  exact hkey
