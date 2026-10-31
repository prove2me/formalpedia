-- Prove2me | solution 1 for SAPMM.Regret.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:28:52.31934+00:00
-- url     : https://prove2.me/submissions/efbeff17-898d-4185-bc87-272813dd8b95

import Mathlib
import Definitions.Def_SAPMM_Regret_Model
import Theorems.Thm_SAPMM_Regret_lemma_3_1

open MeasureTheory ProbabilityTheory

namespace SAPMM.Regret.AuxD

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

end SAPMM.Regret.AuxD

open SAPMM.Regret SAPMM.Regret.AuxD

theorem solution {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample μ ξ)
    (P : Problem n p Ξ) (hP : P.Standing) (hPE : P.FiniteExpect (μ.map (ξ 0)))
    (T : ℕ) (hT : 1 ≤ T)
    {x0 : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ P.X0)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsRun P (1 / Real.sqrt T) (Real.sqrt T) x0 ξ x lam) :
    ∀ xs ∈ P.Phi (μ.map (ξ 0)),
      ∫ ω, ∑ t ∈ Finset.range T, P.F (x t ω) (ξ t ω) ∂μ ≤
        ∫ ω, ∑ t ∈ Finset.range T, P.F xs (ξ t ω) ∂μ + P.κo * Real.sqrt T := by
  intro xs hxs
  obtain ⟨hxsX, hg⟩ := hxs
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hα : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  have hσ : 0 < 1 / Real.sqrt T := by positivity
  have h31 := SAPMM.Regret.lemma_3_1 P hP hσ hα hx0 ξ x lam hrun T
  have hconst : P.κf ^ 2 / (2 * Real.sqrt T) * T + Real.sqrt T / 2 * P.D0 ^ 2
      + 1 / Real.sqrt T / 2 * P.νg ^ 2 * T = P.κo * Real.sqrt T := by
    have key : ∀ s : ℝ, 0 < s → P.κf ^ 2 / (2 * s) * (s * s) + s / 2 * P.D0 ^ 2
        + 1 / s / 2 * P.νg ^ 2 * (s * s) = P.κo * s := by
      intro s hs
      simp only [Problem.κo]
      field_simp
    have := key (Real.sqrt T) hα
    rwa [Real.mul_self_sqrt hTpos.le] at this
  have hmeasξ := hξ.meas
  -- measurability of the integrands
  have hGy_meas : ∀ (y : EuclideanSpace ℝ (Fin n)), Measurable (fun z => P.G y z) :=
    fun y => hP.G_meas.comp (measurable_const.prodMk measurable_id)
  have hFy_meas : ∀ (y : EuclideanSpace ℝ (Fin n)), Measurable (fun z => P.F y z) :=
    fun y => hP.F_meas.comp (measurable_const.prodMk measurable_id)
  have hx_meas : ∀ t, Measurable (x t) :=
    fun t => (hrun.x_meas t).mono (hist_le hmeasξ t) le_rfl
  have hlam_meas : ∀ t, Measurable (lam t) :=
    fun t => (lam_meas hP hrun t).mono (hist_le hmeasξ t) le_rfl
  -- integrability of F(y, ξ_t)
  have hFint : ∀ y ∈ P.O0, ∀ t, Integrable (fun ω => P.F y (ξ t ω)) μ := by
    intro y hy t
    have h0 := hPE.F_int y hy
    rw [integrable_map_measure (hFy_meas y).aestronglyMeasurable (hmeasξ 0).aemeasurable] at h0
    exact ((hξ.ident t).comp (hFy_meas y)).integrable_iff.2 h0
  have hFxint : ∀ t, Integrable (fun ω => P.F (x t ω) (ξ t ω)) μ := by
    intro t
    have hm : Measurable (fun ω => P.F (x t ω) (ξ t ω)) :=
      hP.F_meas.comp ((hx_meas t).prodMk (hmeasξ t))
    refine Integrable.mono' ((hFint x0 (hP.X0_sub_O0 hx0) t).abs.add (integrable_const P.νf))
      hm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    have hxt := hP.X0_sub_O0 (x_mem hrun hx0 t ω)
    have h1 := hP.F_osc _ hxt _ (hP.X0_sub_O0 hx0) (ξ t ω)
    have h2 := hP.F_osc _ (hP.X0_sub_O0 hx0) _ hxt (ξ t ω)
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_le]
    constructor
    · have := neg_abs_le (P.F x0 (ξ t ω)); linarith
    · have := le_abs_self (P.F x0 (ξ t ω)); linarith
  -- the inner-product terms
  have hinner : ∀ t, Integrable (fun ω => inner ℝ (lam t ω) (P.G xs (ξ t ω))) μ ∧
      ∫ ω, inner ℝ (lam t ω) (P.G xs (ξ t ω)) ∂μ ≤ 0 := by
    intro t
    have hcomp : ∀ i, Integrable (fun ω => lam t ω i * P.G xs (ξ t ω) i) μ ∧
        ∫ ω, lam t ω i * P.G xs (ξ t ω) i ∂μ ≤ 0 := by
      intro i
      have hev : Continuous (fun y : EuclideanSpace ℝ (Fin p) => y i) := by fun_prop
      have hli : Measurable[hist ξ t] (fun ω => lam t ω i) :=
        hev.measurable.comp (lam_meas hP hrun t)
      have hGi : Measurable (fun z => P.G xs z i) := hev.measurable.comp (hGy_meas xs)
      have hgi : Measurable[MeasurableSpace.comap (ξ t) (inferInstance : MeasurableSpace Ξ)]
          (fun ω => P.G xs (ξ t ω) i) := hGi.comp (comap_measurable (ξ t))
      have hind := indepFun_hist hξ hli hgi
      have hli' : Measurable (fun ω => lam t ω i) := hli.mono (hist_le hmeasξ t) le_rfl
      have hgi' : Measurable (fun ω => P.G xs (ξ t ω) i) := hGi.comp (hmeasξ t)
      have hbl : ∀ ω, ‖lam t ω i‖ ≤ t * ((1 / Real.sqrt T) * P.νg) := by
        intro ω
        refine le_trans ?_ (lam_bdd hP hσ hrun t ω)
        have := PiLp.norm_apply_le (p := 2) (lam t ω) i
        simpa using this
      have hbg : ∀ ω, ‖P.G xs (ξ t ω) i‖ ≤ P.νg := by
        intro ω
        refine le_trans ?_ (hP.G_bdd xs (hP.X0_sub_O0 hxsX) (ξ t ω))
        have := PiLp.norm_apply_le (p := 2) (P.G xs (ξ t ω)) i
        simpa using this
      have hint1 : Integrable (fun ω => lam t ω i) μ :=
        Integrable.of_bound hli'.aestronglyMeasurable _ (Filter.Eventually.of_forall hbl)
      have hint2 : Integrable (fun ω => P.G xs (ξ t ω) i) μ :=
        Integrable.of_bound hgi'.aestronglyMeasurable _ (Filter.Eventually.of_forall hbg)
      constructor
      · refine Integrable.of_bound (hli'.mul hgi').aestronglyMeasurable
          (t * ((1 / Real.sqrt T) * P.νg) * P.νg) (Filter.Eventually.of_forall fun ω => ?_)
        rw [norm_mul]
        exact mul_le_mul (hbl ω) (hbg ω) (norm_nonneg _) (le_trans (norm_nonneg _) (hbl ω))
      · have := hind.integral_mul_eq_mul_integral hli'.aestronglyMeasurable
          hgi'.aestronglyMeasurable
        simp only [Pi.mul_apply] at this
        rw [this]
        have hE : ∫ ω, P.G xs (ξ t ω) i ∂μ = P.g (μ.map (ξ 0)) i xs := by
          have h1 := ((hξ.ident t).comp hGi).integral_eq
          simp only [Function.comp_def] at h1
          rw [h1, Problem.g, integral_map (hmeasξ 0).aemeasurable hGi.aestronglyMeasurable]
        rw [hE]
        exact mul_nonpos_of_nonneg_of_nonpos
          (integral_nonneg fun ω => lam_nonneg hrun t ω i) (hg i)
    have e : (fun ω => inner ℝ (lam t ω) (P.G xs (ξ t ω))) =
        fun ω => ∑ i, lam t ω i * P.G xs (ξ t ω) i := by
      funext ω; exact inner_eq_sum _ _
    rw [e]
    refine ⟨integrable_finsetSum _ fun i _ => (hcomp i).1, ?_⟩
    rw [integral_finsetSum _ fun i _ => (hcomp i).1]
    exact Finset.sum_nonpos fun i _ => (hcomp i).2
  -- assemble
  have hL : Integrable (fun ω => ∑ t ∈ Finset.range T, P.F (x t ω) (ξ t ω)) μ :=
    integrable_finsetSum _ fun t _ => hFxint t
  have hR1 : Integrable (fun ω => ∑ t ∈ Finset.range T, P.F xs (ξ t ω)) μ :=
    integrable_finsetSum _ fun t _ => hFint xs (hP.X0_sub_O0 hxsX) t
  have hR3 : Integrable (fun ω => ∑ t ∈ Finset.range T, inner ℝ (lam t ω) (P.G xs (ξ t ω))) μ :=
    integrable_finsetSum _ fun t _ => (hinner t).1
  set C := P.κf ^ 2 / (2 * Real.sqrt T) * T + Real.sqrt T / 2 * P.D0 ^ 2
      + 1 / Real.sqrt T / 2 * P.νg ^ 2 * T with hC
  have hR12 : Integrable (fun ω => ∑ t ∈ Finset.range T, P.F xs (ξ t ω) + C) μ :=
    hR1.add (integrable_const C)
  have hmono : ∫ ω, ∑ t ∈ Finset.range T, P.F (x t ω) (ξ t ω) ∂μ ≤
      ∫ ω, ((∑ t ∈ Finset.range T, P.F xs (ξ t ω) + C)
        + ∑ t ∈ Finset.range T, inner ℝ (lam t ω) (P.G xs (ξ t ω))) ∂μ := by
    apply integral_mono hL (hR12.add hR3)
    intro ω
    have := h31 ω xs hxsX
    simp only [Pi.add_apply]
    linarith
  rw [integral_add hR12 hR3, integral_add hR1 (integrable_const C),
    integral_const, integral_finsetSum _ fun t _ => (hinner t).1] at hmono
  simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
  have hneg : ∑ t ∈ Finset.range T, ∫ ω, inner ℝ (lam t ω) (P.G xs (ξ t ω)) ∂μ ≤ 0 :=
    Finset.sum_nonpos fun t _ => (hinner t).2
  rw [← hconst]
  linarith
