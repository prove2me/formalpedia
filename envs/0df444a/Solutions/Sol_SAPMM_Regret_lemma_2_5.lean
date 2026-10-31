-- Prove2me | solution 1 for SAPMM.Regret.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:28:53.338966+00:00
-- url     : https://prove2.me/submissions/ed928880-db50-4f5a-8aca-bcc3de08f038

import Mathlib
import Definitions.Def_SAPMM_Regret_Model

open MeasureTheory ProbabilityTheory

namespace SAPMM.Regret.AuxF

open SAPMM.Regret

lemma projPos_apply {p : ℕ} (y : EuclideanSpace ℝ (Fin p)) (i : Fin p) :
    projPos y i = max (y i) 0 := rfl

lemma norm_sq_sum {p : ℕ} (y : EuclideanSpace ℝ (Fin p)) : ‖y‖ ^ 2 = ∑ i, (y i) ^ 2 :=
  EuclideanSpace.real_norm_sq_eq y

lemma norm_le_of_sum {p : ℕ} {a b : EuclideanSpace ℝ (Fin p)}
    (h : ∑ i, (a i) ^ 2 ≤ ∑ i, (b i) ^ 2) : ‖a‖ ≤ ‖b‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_sum, norm_sq_sum]
  exact h

lemma norm_projPos_le {p : ℕ} (y : EuclideanSpace ℝ (Fin p)) : ‖projPos y‖ ≤ ‖y‖ := by
  apply norm_le_of_sum
  apply Finset.sum_le_sum
  intro i _
  rw [projPos_apply]
  rcases le_total (y i) 0 with h | h
  · rw [max_eq_right h]; simpa using sq_nonneg (y i)
  · rw [max_eq_left h]

lemma projPos_lip {p : ℕ} (a b : EuclideanSpace ℝ (Fin p)) :
    ‖projPos a - projPos b‖ ≤ ‖a - b‖ := by
  apply norm_le_of_sum
  apply Finset.sum_le_sum
  intro i _
  simp only [PiLp.sub_apply, projPos_apply]
  have := abs_max_sub_max_le_abs (a i) (b i) 0
  rw [← sq_abs (max (a i) 0 - max (b i) 0), ← sq_abs (a i - b i)]
  exact pow_le_pow_left₀ (abs_nonneg _) this 2

lemma projPos_of_nonneg {p : ℕ} (y : EuclideanSpace ℝ (Fin p)) (h : ∀ i, 0 ≤ y i) :
    projPos y = y := by
  ext i
  rw [projPos_apply, max_eq_left (h i)]

section run

variable {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  {P : Problem n p Ξ} {σ α : ℝ} {x0 : EuclideanSpace ℝ (Fin n)} {ξ : ℕ → Ω → Ξ}
  {x : ℕ → Ω → EuclideanSpace ℝ (Fin n)} {lam : ℕ → Ω → EuclideanSpace ℝ (Fin p)}

lemma lam_nonneg (hrun : IsRun P σ α x0 ξ x lam) : ∀ t ω i, 0 ≤ lam t ω i := by
  intro t ω i
  cases t with
  | zero => rw [hrun.lam_zero]; simp
  | succ t => rw [hrun.lam_succ, projPos_apply]; exact le_max_right _ _

lemma x_mem (hrun : IsRun P σ α x0 ξ x lam) (hx0 : x0 ∈ P.X0) : ∀ t ω, x t ω ∈ P.X0 := by
  intro t ω
  cases t with
  | zero => rw [hrun.x_zero]; exact hx0
  | succ t => exact hrun.x_mem t ω

end run




lemma projPos_cont {p : ℕ} : Continuous (projPos (p := p)) := by
  unfold projPos; fun_prop

lemma inner_eq_sum {p : ℕ} (a b : EuclideanSpace ℝ (Fin p)) : inner ℝ a b = ∑ i, a i * b i := by
  simp [PiLp.inner_apply, mul_comm]

section prob

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

lemma hist_mono (ξ : ℕ → Ω → Ξ) {s t : ℕ} (h : s ≤ t) : hist ξ s ≤ hist ξ t := by
  unfold hist
  apply biSup_mono
  intro j hj
  simp only [Finset.mem_range] at hj ⊢
  omega

lemma hist_le {ξ : ℕ → Ω → Ξ} (hξ : ∀ t, Measurable (ξ t)) (t : ℕ) :
    hist ξ t ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun j _ => (hξ j).comap_le

lemma meas_xi_hist (ξ : ℕ → Ω → Ξ) {j t : ℕ} (h : j < t) : Measurable[hist ξ t] (ξ j) := by
  rw [measurable_iff_comap_le]
  exact le_iSup₂ (f := fun j (_ : j ∈ Finset.range t) =>
    MeasurableSpace.comap (ξ j) (inferInstance : MeasurableSpace Ξ)) j (Finset.mem_range.2 h)

lemma hist_indep {μ : Measure Ω} {ξ : ℕ → Ω → Ξ} (hξ : IsIIDSample μ ξ) (t : ℕ) :
    Indep (hist ξ t) (MeasurableSpace.comap (ξ t) (inferInstance : MeasurableSpace Ξ)) μ := by
  have h := indep_iSup_of_disjoint
    (m := fun j => MeasurableSpace.comap (ξ j) (inferInstance : MeasurableSpace Ξ))
    (fun j => (hξ.meas j).comap_le) hξ.indep.iIndep
    (S := ((Finset.range t : Finset ℕ) : Set ℕ)) (T := {t}) (by simp)
  convert h using 1
  · simp [hist]
  · simp

lemma indepFun_hist {μ : Measure Ω} {ξ : ℕ → Ω → Ξ} (hξ : IsIIDSample μ ξ) {t : ℕ}
    {f g : Ω → ℝ} (hf : Measurable[hist ξ t] f)
    (hg : Measurable[MeasurableSpace.comap (ξ t) (inferInstance : MeasurableSpace Ξ)] g) :
    IndepFun f g μ := by
  have hI := hist_indep hξ t
  rw [IndepFun_iff]
  intro t1 t2 h1 h2
  obtain ⟨s1, hs1, rfl⟩ := h1
  obtain ⟨s2, hs2, rfl⟩ := h2
  exact (Indep_iff _ _ _).1 hI _ _ (hf hs1) (hg hs2)

variable {n p : ℕ} {P : Problem n p Ξ} {σ α : ℝ} {x0 : EuclideanSpace ℝ (Fin n)}
  {ξ : ℕ → Ω → Ξ} {x : ℕ → Ω → EuclideanSpace ℝ (Fin n)}
  {lam : ℕ → Ω → EuclideanSpace ℝ (Fin p)}

lemma lam_meas (hP : P.Standing) (hrun : IsRun P σ α x0 ξ x lam) :
    ∀ t, Measurable[hist ξ t] (lam t) := by
  intro t
  induction t with
  | zero =>
    have : lam 0 = fun _ => 0 := funext hrun.lam_zero
    rw [this]; exact measurable_const
  | succ t ih =>
    have e : lam (t + 1) = fun ω => projPos (lam t ω + σ • P.G (x (t + 1) ω) (ξ t ω)) :=
      funext (hrun.lam_succ t)
    rw [e]
    have h1 : Measurable[hist ξ (t + 1)] (lam t) := ih.mono (hist_mono ξ (Nat.le_succ t)) le_rfl
    have h2 : Measurable[hist ξ (t + 1)] (fun ω => P.G (x (t + 1) ω) (ξ t ω)) :=
      hP.G_meas.comp ((hrun.x_meas (t + 1)).prodMk (meas_xi_hist ξ (Nat.lt_succ_self t)))
    exact projPos_cont.measurable.comp (h1.add (h2.const_smul σ))

lemma lam_step (hP : P.Standing) (hσ : 0 < σ) (hrun : IsRun P σ α x0 ξ x lam) :
    ∀ t ω, ‖lam (t + 1) ω‖ ≤ ‖lam t ω‖ + σ * P.νg := by
  intro t ω
  have hG : ‖P.G (x (t + 1) ω) (ξ t ω)‖ ≤ P.νg :=
    hP.G_bdd _ (hP.X0_sub_O0 (hrun.x_mem t ω)) _
  have h1 := projPos_lip (lam t ω + σ • P.G (x (t + 1) ω) (ξ t ω)) (lam t ω)
  rw [projPos_of_nonneg (lam t ω) (lam_nonneg hrun t ω), add_sub_cancel_left,
    ← hrun.lam_succ, norm_smul, Real.norm_eq_abs, abs_of_pos hσ] at h1
  have := norm_sub_norm_le (lam (t + 1) ω) (lam t ω)
  have := mul_le_mul_of_nonneg_left hG hσ.le
  linarith

lemma lam_bdd (hP : P.Standing) (hσ : 0 < σ) (hrun : IsRun P σ α x0 ξ x lam) :
    ∀ t ω, ‖lam t ω‖ ≤ t * (σ * P.νg) := by
  intro t ω
  induction t with
  | zero => rw [hrun.lam_zero]; simp
  | succ t ih =>
    have := lam_step hP hσ hrun t ω
    push_cast
    linarith

end prob


lemma norm_le_sum_of_nonneg {p : ℕ} (y : EuclideanSpace ℝ (Fin p)) (h : ∀ i, 0 ≤ y i) :
    ‖y‖ ≤ ∑ i, y i := by
  rw [← sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ => h i), norm_sq_sum]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => h i

end SAPMM.Regret.AuxF

open SAPMM.Regret SAPMM.Regret.AuxF

theorem solution {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample μ ξ)
    (P : Problem n p Ξ) (hP : P.Standing) (hPE : P.FiniteExpect (μ.map (ξ 0)))
    (hS : P.Slater (μ.map (ξ 0))) {σ α : ℝ} (hσ : 0 < σ) (hα : 0 < α)
    {x0 : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ P.X0)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsRun P σ α x0 ξ x lam) :
    ∀ t1 k : ℕ, k ≤ t1 →
      μ[fun ω => inner ℝ (lam t1 ω) (P.G P.xhat (ξ t1 ω)) | hist ξ k] ≤ᵐ[μ]
        fun ω => -P.ε0 * μ[fun ω => ‖lam t1 ω‖ | hist ξ k] ω := by
  intro t1 k hk
  have hmeasξ := hξ.meas
  have hle : hist ξ k ≤ hist ξ t1 := hist_mono ξ hk
  have hle1 : hist ξ t1 ≤ ‹MeasurableSpace Ω› := hist_le hmeasξ t1
  have hxhO : P.xhat ∈ P.O0 := hP.X0_sub_O0 hS.xhat_mem
  have hev : ∀ i : Fin p, Continuous (fun y : EuclideanSpace ℝ (Fin p) => y i) :=
    fun i => by fun_prop
  have hGy_meas : Measurable (fun z => P.G P.xhat z) :=
    hP.G_meas.comp (measurable_const.prodMk measurable_id)
  set f : Fin p → Ω → ℝ := fun i ω => lam t1 ω i with hf
  set h : Fin p → Ω → ℝ := fun i ω => P.G P.xhat (ξ t1 ω) i with hh
  have hf_m : ∀ i, Measurable[hist ξ t1] (f i) :=
    fun i => (hev i).measurable.comp (lam_meas hP hrun t1)
  have hf_m' : ∀ i, Measurable (f i) := fun i => (hf_m i).mono hle1 le_rfl
  have hGi : ∀ i, Measurable (fun z => P.G P.xhat z i) := fun i => (hev i).measurable.comp hGy_meas
  have hh_m : ∀ i, Measurable[MeasurableSpace.comap (ξ t1) (inferInstance : MeasurableSpace Ξ)]
      (h i) := fun i => (hGi i).comp (comap_measurable (ξ t1))
  have hh_m' : ∀ i, Measurable (h i) := fun i => (hGi i).comp (hmeasξ t1)
  have hfb : ∀ i ω, ‖f i ω‖ ≤ t1 * (σ * P.νg) := by
    intro i ω
    refine le_trans ?_ (lam_bdd hP hσ hrun t1 ω)
    have := PiLp.norm_apply_le (p := 2) (lam t1 ω) i
    simpa using this
  have hhb : ∀ i ω, ‖h i ω‖ ≤ P.νg := by
    intro i ω
    refine le_trans ?_ (hP.G_bdd P.xhat hxhO (ξ t1 ω))
    have := PiLp.norm_apply_le (p := 2) (P.G P.xhat (ξ t1 ω)) i
    simpa using this
  have hfint : ∀ i, Integrable (f i) μ := fun i =>
    Integrable.of_bound (hf_m' i).aestronglyMeasurable _ (Filter.Eventually.of_forall (hfb i))
  have hhint : ∀ i, Integrable (h i) μ := fun i =>
    Integrable.of_bound (hh_m' i).aestronglyMeasurable _ (Filter.Eventually.of_forall (hhb i))
  have hfhint : ∀ i, Integrable (f i * h i) μ := fun i =>
    (hhint i).bdd_mul (hf_m' i).aestronglyMeasurable (Filter.Eventually.of_forall (hfb i))
  have hc : ∀ i, ∫ ω, h i ω ∂μ = P.g (μ.map (ξ 0)) i P.xhat := by
    intro i
    have h1 := ((hξ.ident t1).comp (hGi i)).integral_eq
    simp only [Function.comp_def] at h1
    simp only [hh]
    rw [h1, Problem.g, integral_map (hmeasξ 0).aemeasurable (hGi i).aestronglyMeasurable]
  have hcomp : ∀ i, ∀ᵐ ω ∂μ, μ[f i * h i | hist ξ k] ω =
      P.g (μ.map (ξ 0)) i P.xhat * μ[f i | hist ξ k] ω := by
    intro i
    have h1 : μ[h i | hist ξ t1] =ᵐ[μ] fun _ => ∫ ω, h i ω ∂μ :=
      condExp_indep_eq (hmeasξ t1).comap_le hle1 (hh_m i).stronglyMeasurable
        (hist_indep hξ t1).symm
    have h2 : μ[f i * h i | hist ξ t1] =ᵐ[μ] f i * μ[h i | hist ξ t1] :=
      condExp_mul_of_stronglyMeasurable_left (hf_m i).stronglyMeasurable (hfhint i) (hhint i)
    have h3 : μ[f i * h i | hist ξ t1] =ᵐ[μ] (∫ ω, h i ω ∂μ) • f i := by
      filter_upwards [h2, h1] with ω hω1 hω2
      rw [hω1, Pi.mul_apply, hω2, Pi.smul_apply, smul_eq_mul, mul_comm]
    have h4 : μ[f i * h i | hist ξ k] =ᵐ[μ] μ[μ[f i * h i | hist ξ t1] | hist ξ k] :=
      (condExp_condExp_of_le hle hle1).symm
    have h5 : μ[μ[f i * h i | hist ξ t1] | hist ξ k] =ᵐ[μ] μ[(∫ ω, h i ω ∂μ) • f i | hist ξ k] :=
      condExp_congr_ae h3
    have h6 := condExp_smul (μ := μ) (∫ ω, h i ω ∂μ) (f i) (hist ξ k)
    filter_upwards [h4, h5, h6] with ω hω4 hω5 hω6
    rw [hω4, hω5, hω6, Pi.smul_apply, smul_eq_mul, hc i]
  have e : (fun ω => inner ℝ (lam t1 ω) (P.G P.xhat (ξ t1 ω))) = ∑ i, f i * h i := by
    funext ω
    rw [Finset.sum_apply, inner_eq_sum]
    rfl
  have hsum : μ[fun ω => inner ℝ (lam t1 ω) (P.G P.xhat (ξ t1 ω)) | hist ξ k] =ᵐ[μ]
      ∑ i, μ[f i * h i | hist ξ k] := by
    rw [e]; exact condExp_finsetSum (fun i _ => hfhint i) _
  have hnonneg : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ μ[f i | hist ξ k] ω := fun i =>
    condExp_nonneg (Filter.Eventually.of_forall fun ω => lam_nonneg hrun t1 ω i)
  have hnorm_int : Integrable (fun ω => ‖lam t1 ω‖) μ :=
    Integrable.of_bound ((lam_meas hP hrun t1).mono hle1 le_rfl).norm.aestronglyMeasurable
      (t1 * (σ * P.νg)) (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact lam_bdd hP hσ hrun t1 ω)
  have hnorm : μ[fun ω => ‖lam t1 ω‖ | hist ξ k] ≤ᵐ[μ] μ[∑ i, f i | hist ξ k] := by
    apply condExp_mono hnorm_int (integrable_finsetSum' _ fun i _ => hfint i)
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Finset.sum_apply]
    exact norm_le_sum_of_nonneg _ (fun i => lam_nonneg hrun t1 ω i)
  have hsumf : μ[∑ i, f i | hist ξ k] =ᵐ[μ] ∑ i, μ[f i | hist ξ k] :=
    condExp_finsetSum (fun i _ => hfint i) _
  filter_upwards [hsum, ae_all_iff.2 hcomp, ae_all_iff.2 hnonneg, hnorm, hsumf] with
    ω h1 h2 h3 h4 h5
  rw [h1, Finset.sum_apply]
  rw [h5, Finset.sum_apply] at h4
  have : ∑ i, μ[f i * h i | hist ξ k] ω ≤ ∑ i, -P.ε0 * μ[f i | hist ξ k] ω := by
    apply Finset.sum_le_sum
    intro i _
    rw [h2 i]
    exact mul_le_mul_of_nonneg_right (hS.slater i) (h3 i)
  rw [← Finset.mul_sum] at this
  have := mul_le_mul_of_nonneg_left h4 hS.ε0_pos.le
  linarith
