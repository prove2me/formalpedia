-- Prove2me | solution 1 for SAPMM.Regret.lemma_2_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:35:48.362855+00:00
-- url     : https://prove2.me/submissions/64537b27-1fa8-4357-a562-f3c71fa50f6f

import Mathlib
import Definitions.Def_SAPMM_Regret_Model
import Theorems.Thm_SAPMM_Regret_lemma_2_1
import Theorems.Thm_SAPMM_Regret_lemma_2_3
import Theorems.Thm_SAPMM_Regret_lemma_2_5

open MeasureTheory ProbabilityTheory

namespace SAPMM.Regret.AuxG

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


lemma sum_range_cast (s : ℕ) : ∑ j ∈ Finset.range s, (j : ℝ) = s * ((s : ℝ) - 1) / 2 := by
  induction s with
  | zero => simp
  | succ s ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

end SAPMM.Regret.AuxG

open SAPMM.Regret SAPMM.Regret.AuxG

theorem solution {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample μ ξ)
    (P : Problem n p Ξ) (hP : P.Standing) (hPE : P.FiniteExpect (μ.map (ξ 0)))
    (hS : P.Slater (μ.map (ξ 0))) {σ α : ℝ} (hσ : 0 < σ) (hα : 0 < α)
    {x0 : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ P.X0)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsRun P σ α x0 ξ x lam)
    (s : ℕ) (hs : 1 ≤ s) (t : ℕ) (ht : 1 ≤ t) :
    (∀ ω, |‖lam (t + 1) ω‖ - ‖lam t ω‖| ≤ σ * P.νg) ∧
      ∀ᵐ ω ∂μ, μ[fun ω => ‖lam (t + s) ω‖ - ‖lam t ω‖ | hist ξ t] ω ≤
        if ‖lam t ω‖ < P.vartheta σ α s then (s : ℝ) * σ * P.νg
        else -((s : ℝ) * σ * P.ε0 / 2) := by
  have h21 := SAPMM.Regret.lemma_2_1 P hP hσ hα hx0 ξ x lam hrun
  have h23 := SAPMM.Regret.lemma_2_3 P hP hσ hα hx0 ξ x lam hrun
  have h25 := SAPMM.Regret.lemma_2_5 μ ξ hξ P hP hPE hS hσ hα hx0 x lam hrun
  refine ⟨fun ω => abs_le.2 ⟨by linarith [(h21 t ω).2.1], by linarith [(h21 t ω).2.2]⟩, ?_⟩
  have hmeasξ := hξ.meas
  have hm : hist ξ t ≤ ‹MeasurableSpace Ω› := hist_le hmeasξ t
  have hε := hS.ε0_pos
  have hνg := hP.νg_pos
  have hνf := hP.νf_pos
  have hD0 := hP.D0_pos
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  set xh := P.xhat with hxh
  have hxhX : xh ∈ P.X0 := hS.xhat_mem
  have hxhO : xh ∈ P.O0 := hP.X0_sub_O0 hxhX
  -- measurability and bounds
  have hlamm : ∀ l, Measurable (lam l) := fun l => (lam_meas hP hrun l).mono (hist_le hmeasξ l) le_rfl
  have hNm : ∀ l, Measurable (fun ω => ‖lam l ω‖) := fun l => (hlamm l).norm
  have hNb : ∀ l ω, |‖lam l ω‖| ≤ l * (σ * P.νg) := fun l ω => by
    rw [abs_of_nonneg (norm_nonneg _)]; exact lam_bdd hP hσ hrun l ω
  have intb : ∀ (f : Ω → ℝ) (C : ℝ), Measurable f → (∀ ω, |f ω| ≤ C) → Integrable f μ :=
    fun f C hf hb => Integrable.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hb ω)
  have hNint : ∀ l, Integrable (fun ω => ‖lam l ω‖) μ := fun l => intb _ _ (hNm l) (hNb l)
  have hNt_m : Measurable[hist ξ t] (fun ω => ‖lam t ω‖) :=
    measurable_norm.comp (lam_meas hP hrun t)
  have hNt_sm : StronglyMeasurable[hist ξ t] (fun ω => ‖lam t ω‖) := hNt_m.stronglyMeasurable
  have hGm : Measurable (fun z => P.G xh z) := hP.G_meas.comp (measurable_const.prodMk measurable_id)
  set I : ℕ → Ω → ℝ := fun l ω => inner ℝ (lam l ω) (P.G xh (ξ l ω)) with hI
  have hIm : ∀ l, Measurable (I l) := fun l =>
    (hlamm l).inner (hGm.comp (hmeasξ l))
  have hIb : ∀ l ω, |I l ω| ≤ l * (σ * P.νg) * P.νg := by
    intro l ω
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    exact mul_le_mul (lam_bdd hP hσ hrun l ω) (hP.G_bdd xh hxhO (ξ l ω)) (norm_nonneg _)
      (by positivity)
  have hIint : ∀ l, Integrable (I l) μ := fun l => intb _ _ (hIm l) (hIb l)
  -- increments of ‖λ‖
  have hinc : ∀ j ω, ‖lam t ω‖ - j * (σ * P.νg) ≤ ‖lam (t + j) ω‖ ∧
      ‖lam (t + j) ω‖ ≤ ‖lam t ω‖ + j * (σ * P.νg) := by
    intro j ω
    induction j with
    | zero => simp
    | succ j ih =>
      have := h21 (t + j) ω
      rw [← add_assoc]
      push_cast
      constructor <;> linarith [this.2.1, this.2.2, ih.1, ih.2]
  -- one step of (2.16), multiplied by 2σ
  have step : ∀ l ω, ‖lam (l + 1) ω‖ ^ 2 ≤ ‖lam l ω‖ ^ 2 + 2 * σ * P.νf + 2 * σ * I l ω
      + σ ^ 2 * P.νg ^ 2 + α * σ * (‖xh - x l ω‖ ^ 2 - ‖xh - x (l + 1) ω‖ ^ 2) := by
    intro l ω
    have h1 := h23 l ω xh hxhX
    have hG : ‖P.G xh (ξ l ω)‖ ≤ P.νg := hP.G_bdd _ hxhO _
    have hsG : ‖σ • P.G xh (ξ l ω)‖ = σ * ‖P.G xh (ξ l ω)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hσ]
    have h2 : ‖projPos (lam l ω + σ • P.G xh (ξ l ω))‖ ^ 2 ≤
        ‖lam l ω + σ • P.G xh (ξ l ω)‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_projPos_le _) 2
    rw [norm_add_sq_real, hsG, real_inner_smul_right] at h2
    have h3 : ‖P.G xh (ξ l ω)‖ ^ 2 ≤ P.νg ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hG 2
    have hF := hP.F_osc xh hxhO (x (l + 1) ω) (hP.X0_sub_O0 (hrun.x_mem l ω)) (ξ l ω)
    have h1' := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * σ)
    have e1 : 2 * σ * (P.F (x (l + 1) ω) (ξ l ω) + 1 / (2 * σ) * ‖lam (l + 1) ω‖ ^ 2
        + α / 2 * ‖x (l + 1) ω - x l ω‖ ^ 2) = 2 * σ * P.F (x (l + 1) ω) (ξ l ω)
        + ‖lam (l + 1) ω‖ ^ 2 + α * σ * ‖x (l + 1) ω - x l ω‖ ^ 2 := by
      field_simp
    have e2 : 2 * σ * (P.F xh (ξ l ω) + 1 / (2 * σ) * ‖projPos (lam l ω + σ • P.G xh (ξ l ω))‖ ^ 2
        + α / 2 * (‖xh - x l ω‖ ^ 2 - ‖xh - x (l + 1) ω‖ ^ 2)) = 2 * σ * P.F xh (ξ l ω)
        + ‖projPos (lam l ω + σ • P.G xh (ξ l ω))‖ ^ 2
        + α * σ * (‖xh - x l ω‖ ^ 2 - ‖xh - x (l + 1) ω‖ ^ 2) := by
      field_simp
    rw [e1, e2] at h1'
    have : 0 ≤ α * σ * ‖x (l + 1) ω - x l ω‖ ^ 2 := by positivity
    have hI' : I l ω = inner ℝ (lam l ω) (P.G xh (ξ l ω)) := rfl
    have := mul_le_mul_of_nonneg_left hF (by positivity : (0 : ℝ) ≤ 2 * σ)
    nlinarith [sq_nonneg σ]
  -- summed over s steps
  have hsum : ∀ j ω, ‖lam (t + j) ω‖ ^ 2 ≤ ‖lam t ω‖ ^ 2 + j * (2 * σ * P.νf + σ ^ 2 * P.νg ^ 2)
      + 2 * σ * ∑ i ∈ Finset.range j, I (t + i) ω
      + α * σ * (‖xh - x t ω‖ ^ 2 - ‖xh - x (t + j) ω‖ ^ 2) := by
    intro j ω
    induction j with
    | zero => simp
    | succ j ih =>
      have := step (t + j) ω
      rw [Finset.sum_range_succ, ← add_assoc]
      push_cast
      nlinarith
  set C0 := s * (2 * σ * P.νf + σ ^ 2 * P.νg ^ 2) + α * σ * P.D0 ^ 2 with hC0
  have hpath : ∀ ω, ‖lam (t + s) ω‖ ^ 2 ≤ ‖lam t ω‖ ^ 2 + C0
      + 2 * σ * ∑ i ∈ Finset.range s, I (t + i) ω := by
    intro ω
    have h1 := hsum s ω
    have h2 : ‖xh - x t ω‖ ^ 2 ≤ P.D0 ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hP.diam xh hxhX (x t ω) (x_mem hrun hx0 t ω)) 2
    have h3 : 0 ≤ ‖xh - x (t + s) ω‖ ^ 2 := sq_nonneg _
    have h4 : 0 < α * σ := mul_pos hα hσ
    nlinarith
  -- conditional expectations
  have hN2int : ∀ l, Integrable (fun ω => ‖lam l ω‖ ^ 2) μ := fun l =>
    intb _ ((l * (σ * P.νg)) ^ 2) ((hNm l).pow_const 2) (fun ω => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (lam_bdd hP hσ hrun l ω) 2)
  have hA_m : Measurable[hist ξ t] (fun ω => ‖lam t ω‖ ^ 2 + C0) :=
    (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin p) => ‖y‖ ^ 2 + C0).measurable.comp
      (lam_meas hP hrun t)
  have hA_sm : StronglyMeasurable[hist ξ t] (fun ω => ‖lam t ω‖ ^ 2 + C0) := hA_m.stronglyMeasurable
  have hAint : Integrable (fun ω => ‖lam t ω‖ ^ 2 + C0) μ := (hN2int t).add (integrable_const C0)
  have hSint : Integrable (∑ i ∈ Finset.range s, I (t + i)) μ :=
    integrable_finsetSum' _ fun i _ => hIint (t + i)
  have hrhs_eq : (fun ω => ‖lam t ω‖ ^ 2 + C0 + 2 * σ * ∑ i ∈ Finset.range s, I (t + i) ω) =
      (fun ω => ‖lam t ω‖ ^ 2 + C0) + (2 * σ) • ∑ i ∈ Finset.range s, I (t + i) := by
    funext ω; simp [Finset.sum_apply]
  have hQ : μ[fun ω => ‖lam (t + s) ω‖ ^ 2 | hist ξ t] ≤ᵐ[μ]
      fun ω => ‖lam t ω‖ ^ 2 + C0 + 2 * σ * ∑ i ∈ Finset.range s, μ[I (t + i) | hist ξ t] ω := by
    have h1 : μ[fun ω => ‖lam (t + s) ω‖ ^ 2 | hist ξ t] ≤ᵐ[μ]
        μ[fun ω => ‖lam t ω‖ ^ 2 + C0 + 2 * σ * ∑ i ∈ Finset.range s, I (t + i) ω | hist ξ t] := by
      apply condExp_mono (hN2int (t + s))
      · rw [hrhs_eq]; exact hAint.add (hSint.smul _)
      · exact Filter.Eventually.of_forall hpath
    rw [hrhs_eq] at h1
    have h2 := condExp_add (m := hist ξ t) hAint (hSint.smul (2 * σ))
    have h3 := condExp_smul (μ := μ) (2 * σ) (∑ i ∈ Finset.range s, I (t + i)) (hist ξ t)
    have h4 := condExp_finsetSum (μ := μ) (s := Finset.range s) (fun i _ => hIint (t + i)) (hist ξ t)
    rw [condExp_of_stronglyMeasurable hm hA_sm hAint] at h2
    filter_upwards [h1, h2, h3, h4] with ω e1 e2 e3 e4
    rw [e2, Pi.add_apply, e3, Pi.smul_apply, e4, Finset.sum_apply, smul_eq_mul] at e1
    exact e1
  -- Lemma 2.5 and the lower bound on ‖λ^{t+i}‖
  have hIc : ∀ i, μ[I (t + i) | hist ξ t] ≤ᵐ[μ]
      fun ω => -P.ε0 * (‖lam t ω‖ - i * (σ * P.νg)) := by
    intro i
    have h1 := h25 (t + i) t (by omega)
    have hlow_m : Measurable[hist ξ t] (fun ω => ‖lam t ω‖ - i * (σ * P.νg)) :=
      (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin p) => ‖y‖ - i * (σ * P.νg)).measurable.comp
        (lam_meas hP hrun t)
    have hlow_sm : StronglyMeasurable[hist ξ t] (fun ω => ‖lam t ω‖ - i * (σ * P.νg)) :=
      hlow_m.stronglyMeasurable
    have hlow_int : Integrable (fun ω => ‖lam t ω‖ - i * (σ * P.νg)) μ :=
      (hNint t).sub (integrable_const _)
    have h2 : μ[fun ω => ‖lam t ω‖ - i * (σ * P.νg) | hist ξ t] ≤ᵐ[μ]
        μ[fun ω => ‖lam (t + i) ω‖ | hist ξ t] :=
      condExp_mono hlow_int (hNint (t + i)) (Filter.Eventually.of_forall fun ω => (hinc i ω).1)
    rw [condExp_of_stronglyMeasurable hm hlow_sm hlow_int] at h2
    filter_upwards [h1, h2] with ω e1 e2
    have := mul_le_mul_of_nonneg_left e2 hε.le
    simp only [hI]
    linarith
  have hQ2 : ∀ᵐ ω ∂μ, μ[fun ω => ‖lam (t + s) ω‖ ^ 2 | hist ξ t] ω ≤
      ‖lam t ω‖ ^ 2 + C0 - 2 * σ * P.ε0 * s * ‖lam t ω‖
        + P.ε0 * σ ^ 2 * P.νg * s * ((s : ℝ) - 1) := by
    filter_upwards [hQ, ae_all_iff.2 hIc] with ω e1 e2
    have h3 : ∑ i ∈ Finset.range s, μ[I (t + i) | hist ξ t] ω ≤
        ∑ i ∈ Finset.range s, -P.ε0 * (‖lam t ω‖ - i * (σ * P.νg)) :=
      Finset.sum_le_sum fun i _ => e2 i
    have h4 : ∑ i ∈ Finset.range s, -P.ε0 * (‖lam t ω‖ - i * (σ * P.νg)) =
        -P.ε0 * s * ‖lam t ω‖ + P.ε0 * σ * P.νg * (s * ((s : ℝ) - 1) / 2) := by
      rw [← sum_range_cast, Finset.mul_sum]
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      · ring
      · apply Finset.sum_congr rfl; intro i _; ring
    rw [h4] at h3
    have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * σ)
    nlinarith
  -- pulling out b = ‖λ^t‖ - ε0 σ s / 2
  set b : Ω → ℝ := fun ω => ‖lam t ω‖ - P.ε0 * σ * s / 2 with hb
  have hb_m : Measurable[hist ξ t] b :=
    (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin p) => ‖y‖ - P.ε0 * σ * s / 2).measurable.comp
      (lam_meas hP hrun t)
  have h2b_m : Measurable[hist ξ t] (fun ω => 2 * b ω) :=
    (by fun_prop : Continuous fun y : ℝ => 2 * y).measurable.comp hb_m
  have hb2_m : Measurable[hist ξ t] (fun ω => b ω ^ 2) :=
    (by fun_prop : Continuous fun y : ℝ => y ^ 2).measurable.comp hb_m
  have hbm' : Measurable b := hb_m.mono hm le_rfl
  have hbb : ∀ ω, |b ω| ≤ t * (σ * P.νg) + P.ε0 * σ * s / 2 := by
    intro ω
    have h1 := hNb t ω
    rw [abs_of_nonneg (norm_nonneg _)] at h1
    have h0 := norm_nonneg (lam t ω)
    have : 0 ≤ P.ε0 * σ * s / 2 := by positivity
    rw [abs_le]; constructor <;> simp only [hb] <;> linarith
  have h2bint : Integrable (fun ω => 2 * b ω) μ :=
    intb _ (2 * (t * (σ * P.νg) + P.ε0 * σ * s / 2)) (h2b_m.mono hm le_rfl)
      (fun ω => by rw [abs_mul, abs_two]; linarith [hbb ω])
  have hb2int : Integrable (fun ω => b ω ^ 2) μ :=
    intb _ ((t * (σ * P.νg) + P.ε0 * σ * s / 2) ^ 2) (hb2_m.mono hm le_rfl)
      (fun ω => by
        rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbb ω) 2)
  have hprodint : Integrable ((fun ω => 2 * b ω) * fun ω => ‖lam (t + s) ω‖) μ :=
    (hNint (t + s)).bdd_mul (c := 2 * (t * (σ * P.νg) + P.ε0 * σ * s / 2))
      (h2b_m.mono hm le_rfl).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul, abs_two]; linarith [hbb ω])
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := hist ξ t) (μ := μ)
    h2b_m.stronglyMeasurable hprodint (hNint (t + s))
  have hsqint : Integrable (fun ω => ‖lam (t + s) ω‖ ^ 2 + b ω ^ 2) μ := (hN2int (t + s)).add hb2int
  have hmono2 : μ[(fun ω => 2 * b ω) * fun ω => ‖lam (t + s) ω‖ | hist ξ t] ≤ᵐ[μ]
      μ[fun ω => ‖lam (t + s) ω‖ ^ 2 + b ω ^ 2 | hist ξ t] := by
    apply condExp_mono hprodint hsqint
    refine Filter.Eventually.of_forall fun ω => ?_
    simp only [Pi.mul_apply]
    nlinarith [sq_nonneg (‖lam (t + s) ω‖ - b ω)]
  have hadd0 := condExp_add (m := hist ξ t) (hN2int (t + s)) hb2int
  rw [condExp_of_stronglyMeasurable hm hb2_m.stronglyMeasurable hb2int] at hadd0
  have hadd : μ[fun ω => ‖lam (t + s) ω‖ ^ 2 + b ω ^ 2 | hist ξ t] =ᵐ[μ]
      μ[fun ω => ‖lam (t + s) ω‖ ^ 2 | hist ξ t] + fun ω => b ω ^ 2 := hadd0
  -- upper bound in the easy case
  have hup_m : Measurable[hist ξ t] (fun ω => ‖lam t ω‖ + s * (σ * P.νg)) :=
    (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin p) => ‖y‖ + s * (σ * P.νg)).measurable.comp
      (lam_meas hP hrun t)
  have hup_int : Integrable (fun ω => ‖lam t ω‖ + s * (σ * P.νg)) μ :=
    (hNint t).add (integrable_const _)
  have hupper : μ[fun ω => ‖lam (t + s) ω‖ | hist ξ t] ≤ᵐ[μ]
      μ[fun ω => ‖lam t ω‖ + s * (σ * P.νg) | hist ξ t] :=
    condExp_mono (hNint (t + s)) hup_int (Filter.Eventually.of_forall fun ω => (hinc s ω).2)
  rw [condExp_of_stronglyMeasurable hm hup_m.stronglyMeasurable hup_int] at hupper
  have hdiff0 := condExp_sub (m := hist ξ t) (hNint (t + s)) (hNint t)
  rw [condExp_of_stronglyMeasurable hm hNt_sm (hNint t)] at hdiff0
  have hdiff : μ[fun ω => ‖lam (t + s) ω‖ - ‖lam t ω‖ | hist ξ t] =ᵐ[μ]
      μ[fun ω => ‖lam (t + s) ω‖ | hist ξ t] - fun ω => ‖lam t ω‖ := hdiff0
  -- constants
  have hϑ : P.ε0 * σ * s * P.vartheta σ α s = P.ε0 ^ 2 * σ ^ 2 * s ^ 2 / 2
      + P.ε0 * P.νg * σ ^ 2 * s * ((s : ℝ) - 1) + α * σ * P.D0 ^ 2 + 2 * σ * P.νf * s
      + σ ^ 2 * P.νg ^ 2 * s := by
    unfold Problem.vartheta
    have : (s : ℝ) ≠ 0 := by positivity
    field_simp
  have hϑpos : P.ε0 * σ * s / 2 < P.vartheta σ α s := by
    unfold Problem.vartheta
    have h1 : 0 ≤ P.νg * σ * ((s : ℝ) - 1) := mul_nonneg (by positivity) (by linarith)
    have h2 : 0 ≤ α * P.D0 ^ 2 / (P.ε0 * s) := by positivity
    have h3 : 0 < 2 * P.νf / P.ε0 := by positivity
    have h4 : 0 ≤ σ * P.νg ^ 2 / P.ε0 := by positivity
    linarith
  filter_upwards [hQ2, hpull, hmono2, hadd, hupper, hdiff] with ω eQ epull emono eadd eup ediff
  rw [ediff, Pi.sub_apply]
  split_ifs with hlt
  · linarith
  · push_neg at hlt
    rw [epull, Pi.mul_apply, eadd, Pi.add_apply] at emono
    set V := μ[fun ω => ‖lam (t + s) ω‖ | hist ξ t] ω
    set Q := μ[fun ω => ‖lam (t + s) ω‖ ^ 2 | hist ξ t] ω
    have hbpos : 0 < b ω := by simp only [hb]; linarith
    have hNs := mul_le_mul_of_nonneg_left hlt (by positivity : (0 : ℝ) ≤ P.ε0 * σ * s)
    have hbsq : b ω ^ 2 = ‖lam t ω‖ ^ 2 - P.ε0 * σ * s * ‖lam t ω‖
        + P.ε0 ^ 2 * σ ^ 2 * s ^ 2 / 4 := by simp only [hb]; ring
    have hQb : Q ≤ b ω ^ 2 := by
      rw [hbsq]
      have hC : C0 = s * (2 * σ * P.νf + σ ^ 2 * P.νg ^ 2) + α * σ * P.D0 ^ 2 := hC0
      have : 0 ≤ P.ε0 ^ 2 * σ ^ 2 * s ^ 2 := by positivity
      linarith only [eQ, hNs, hϑ, hC, this]
    have hVb : V ≤ b ω := by
      have h1 : 2 * b ω * V ≤ 2 * b ω * b ω := by
        calc 2 * b ω * V ≤ Q + b ω ^ 2 := emono
          _ ≤ b ω ^ 2 + b ω ^ 2 := by linarith only [hQb]
          _ = 2 * b ω * b ω := by ring
      exact le_of_mul_le_mul_left h1 (by linarith)
    simp only [hb] at hVb
    linarith
