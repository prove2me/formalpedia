-- Prove2me | solution 1 for SAPMM.Regret.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:42:17.962672+00:00
-- url     : https://prove2.me/submissions/d4201ee8-7047-4581-87d1-fea7686a892f

import Mathlib
import Definitions.Def_SAPMM_Regret_Model
import Theorems.Thm_SAPMM_Regret_lemma_2_1
import Theorems.Thm_SAPMM_Regret_corollary_2_1
import Theorems.Thm_SAPMM_Regret_lemma_2_6
import Theorems.Thm_SAPMM_Regret_lemma_2_7

open MeasureTheory ProbabilityTheory

namespace SAPMM.Regret.AuxH

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



end SAPMM.Regret.AuxH

open SAPMM.Regret SAPMM.Regret.AuxH

theorem solution {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample μ ξ)
    (P : Problem n p Ξ) (hP : P.Standing) (hPE : P.FiniteExpect (μ.map (ξ 0)))
    (hS : P.Slater (μ.map (ξ 0))) (T : ℕ) (hT : 1 ≤ T)
    {x0 : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ P.X0)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsRun P (1 / Real.sqrt T) (Real.sqrt T) x0 ξ x lam)
    (hTp : 2 * (p : ℝ) * P.κg ^ 2 < 3 * (T : ℝ)) :
    ∀ i, ∫ ω, ∑ t ∈ Finset.range T, P.G (x t ω) (ξ t ω) i ∂μ ≤ P.κc * Real.sqrt T := by
  intro i
  have hmeasξ := hξ.meas
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  set q := Real.sqrt T with hq
  have hq1 : 1 ≤ q := by rw [hq]; exact Real.one_le_sqrt.2 hT1
  have hq0 : 0 < q := by linarith
  have hqq : q * q = T := Real.mul_self_sqrt hTpos.le
  set σ := 1 / q with hσdef
  have hσ : 0 < σ := by positivity
  have hσq : σ * q = 1 := by rw [hσdef]; field_simp
  have hε := hS.ε0_pos
  have hνg := hP.νg_pos
  have hνf := hP.νf_pos
  have hD0 := hP.D0_pos
  have hκg := hP.κg_pos
  have hκf := hP.κf_pos
  have hxhO : P.xhat ∈ P.O0 := hP.X0_sub_O0 hS.xhat_mem
  -- ε0 ≤ νg from Slater and (A3)
  have hεν : P.ε0 ≤ P.νg := by
    haveI : IsProbabilityMeasure (μ.map (ξ 0)) :=
      Measure.isProbabilityMeasure_map (hmeasξ 0).aemeasurable
    have h1 := hS.slater i
    have h2 : ∫ z, -P.νg ∂(μ.map (ξ 0)) ≤ ∫ z, P.G P.xhat z i ∂(μ.map (ξ 0)) := by
      apply integral_mono (integrable_const _) (hPE.G_int P.xhat hxhO i)
      intro z
      have := PiLp.norm_apply_le (p := 2) (P.G P.xhat z) i
      have h3 := hP.G_bdd P.xhat hxhO z
      have h4 := neg_abs_le (P.G P.xhat z i)
      simp only [Real.norm_eq_abs] at this
      linarith
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h2
    simp only [Problem.g] at h1
    linarith
  -- the block length s = ⌈√T⌉
  set s := ⌈q⌉₊ with hs_def
  have hsq : q ≤ s := Nat.le_ceil q
  have hsq' : (s : ℝ) < q + 1 := Nat.ceil_lt_add_one hq0.le
  have hs1 : 1 ≤ s := by
    have : (0 : ℝ) < s := lt_of_lt_of_le hq0 hsq
    exact_mod_cast this
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs1
  -- filtration and process
  let ℱ : Filtration ℕ ‹MeasurableSpace Ω› :=
    ⟨hist ξ, fun a b h => hist_mono ξ h, hist_le hmeasξ⟩
  have hℱ0 : ℱ 0 = ⊥ := by
    show hist ξ 0 = ⊥
    simp [hist]
  set Z : ℕ → Ω → ℝ := fun t ω => ‖lam t ω‖ with hZdef
  have hZ : Adapted ℱ Z := fun t => measurable_norm.comp (lam_meas hP hrun t)
  have hZ0 : ∀ ω, Z 0 ω = 0 := fun ω => by simp [hZdef, hrun.lam_zero]
  have h21 := SAPMM.Regret.lemma_2_1 P hP hσ hq0 hx0 ξ x lam hrun
  have hinc : ∀ t ω, |Z (t + 1) ω - Z t ω| ≤ σ * P.νg := fun t ω =>
    abs_le.2 ⟨by simp only [hZdef]; linarith [(h21 t ω).2.1],
      by simp only [hZdef]; linarith [(h21 t ω).2.2]⟩
  have hdrift : ∀ t, 1 ≤ t → ∀ᵐ ω ∂μ,
      μ[fun ω => Z (t + s) ω - Z t ω | ℱ t] ω ≤
        if Z t ω < P.vartheta σ q s then (s : ℝ) * (σ * P.νg) else -((s : ℝ) * (σ * P.ε0 / 2)) := by
    intro t ht
    have h := (SAPMM.Regret.lemma_2_6 μ ξ hξ P hP hPE hS hσ hq0 hx0 x lam hrun s hs1 t ht).2
    filter_upwards [h] with ω hω
    show μ[fun ω => ‖lam (t + s) ω‖ - ‖lam t ω‖ | hist ξ t] ω ≤ _
    by_cases hc : ‖lam t ω‖ < P.vartheta σ q s
    · have hc' : Z t ω < P.vartheta σ q s := hc
      rw [if_pos hc] at hω; rw [if_pos hc']; linarith
    · have hc' : ¬ Z t ω < P.vartheta σ q s := hc
      rw [if_neg hc] at hω; rw [if_neg hc']; linarith
  have hθ : 0 < P.vartheta σ q s := by
    unfold Problem.vartheta
    have h1 : 0 ≤ P.νg * σ * ((s : ℝ) - 1) := mul_nonneg (by positivity) (by
      have : (1 : ℝ) ≤ s := by exact_mod_cast hs1
      linarith)
    have h2 : 0 ≤ q * P.D0 ^ 2 / (P.ε0 * s) := by positivity
    have h3 : 0 < 2 * P.νf / P.ε0 := by positivity
    have h4 : 0 ≤ σ * P.νg ^ 2 / P.ε0 := by positivity
    have h5 : 0 ≤ P.ε0 * σ * s / 2 := by positivity
    linarith
  have hζδ : σ * P.ε0 / 2 ≤ σ * P.νg := by
    have := mul_le_mul_of_nonneg_left hεν hσ.le
    have := mul_pos hσ hε
    linarith
  have h27 := SAPMM.Regret.lemma_2_7 μ ℱ hℱ0 Z hZ hZ0 s hs1 (P.vartheta σ q s) (σ * P.νg)
    (σ * P.ε0 / 2) hθ (by positivity) (by positivity) hζδ hinc hdrift
  -- E‖λ^t‖ ≤ κ*
  have hL : 0 < Real.log (32 * P.νg ^ 2 / P.ε0 ^ 2) := by
    apply Real.log_pos
    rw [one_lt_div (by positivity)]
    nlinarith
  have hEN : ∀ t, ∫ ω, ‖lam t ω‖ ∂μ ≤ P.κstar := by
    have hk0 : 0 < P.κ0 := by unfold Problem.κ0; positivity
    have hk1 : 0 ≤ P.κ1 := by unfold Problem.κ1; positivity
    have hk3 : 0 ≤ P.κ3 := by
      unfold Problem.κ3
      rw [sub_nonneg, le_div_iff₀ hε]
      nlinarith
    have hk4 : 0 < P.κ4 := by unfold Problem.κ4; positivity
    intro t
    rcases Nat.eq_zero_or_pos t with h0 | htpos
    · subst h0
      simp only [hrun.lam_zero, norm_zero, integral_zero]
      unfold Problem.κstar; linarith
    have h1 := h27 t htpos
    simp only [hZdef] at h1
    have hmid : P.vartheta σ q s + (s : ℝ) * (σ * P.νg) + (s : ℝ) * (4 * (σ * P.νg) ^ 2 /
        (σ * P.ε0 / 2)) * Real.log (8 * (σ * P.νg) ^ 2 / (σ * P.ε0 / 2) ^ 2) =
        P.κ0 + P.κ1 * (q / s) + P.κ3 * σ + P.κ4 * (σ * s) := by
      unfold Problem.vartheta Problem.κ0 Problem.κ1 Problem.κ3 Problem.κ4
      have e1 : 4 * (σ * P.νg) ^ 2 / (σ * P.ε0 / 2) = σ * (8 * P.νg ^ 2 / P.ε0) := by
        field_simp; ring
      have e2 : 8 * (σ * P.νg) ^ 2 / (σ * P.ε0 / 2) ^ 2 = 32 * P.νg ^ 2 / P.ε0 ^ 2 := by
        field_simp; ring
      rw [e1, e2]
      field_simp
      ring
    have hqs : q / s ≤ 1 := by rw [div_le_one hsR]; exact hsq
    have hσ1 : σ ≤ 1 := by rw [hσdef, div_le_one hq0]; exact hq1
    have hσs : σ * s ≤ 2 := by
      have h1 := mul_le_mul_of_nonneg_left hsq'.le hσ.le
      have e : σ * (q + 1) = σ * q + σ := by ring
      linarith
    have a1 := mul_le_mul_of_nonneg_left hqs hk1
    have a2 := mul_le_mul_of_nonneg_left hσ1 hk3
    have a3 := mul_le_mul_of_nonneg_left hσs hk4.le
    unfold Problem.κstar
    linarith
  -- Corollary 2.1
  set D := 2 * q - (p : ℝ) * P.κg ^ 2 * σ with hDdef
  have hDq : q / 2 < D := by
    rw [hDdef, hσdef]
    have : (p : ℝ) * P.κg ^ 2 * (1 / q) < 3 / 2 * q := by
      rw [mul_one_div, div_lt_iff₀ hq0]
      nlinarith
    linarith
  have hD : 0 < D := by linarith
  have hc21 := SAPMM.Regret.corollary_2_1 P hP hσ hq0 hx0 ξ x lam hrun hD
  -- integrability
  have hlamm : ∀ l, Measurable (lam l) := fun l => (lam_meas hP hrun l).mono (hist_le hmeasξ l) le_rfl
  have hxm : ∀ l, Measurable (x l) := fun l => (hrun.x_meas l).mono (hist_le hmeasξ l) le_rfl
  have hev : Continuous (fun y : EuclideanSpace ℝ (Fin p) => y i) := by fun_prop
  have intb : ∀ (f : Ω → ℝ) (C : ℝ), Measurable f → (∀ ω, |f ω| ≤ C) → Integrable f μ :=
    fun f C hf hb => Integrable.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hb ω)
  have hGint : ∀ t, Integrable (fun ω => P.G (x t ω) (ξ t ω) i) μ := by
    intro t
    refine intb _ P.νg (hev.measurable.comp (hP.G_meas.comp ((hxm t).prodMk (hmeasξ t))))
      (fun ω => ?_)
    have := PiLp.norm_apply_le (p := 2) (P.G (x t ω) (ξ t ω)) i
    simp only [Real.norm_eq_abs] at this
    exact le_trans this (hP.G_bdd _ (hP.X0_sub_O0 (x_mem hrun hx0 t ω)) _)
  have hNint : ∀ t, Integrable (fun ω => ‖lam t ω‖) μ := fun t =>
    intb _ _ (hlamm t).norm (fun ω => by
      rw [abs_of_nonneg (norm_nonneg _)]; exact lam_bdd hP hσ hrun t ω)
  have hlamTint : Integrable (fun ω => lam T ω i) μ :=
    intb _ _ (hev.measurable.comp (hlamm T)) (fun ω => by
      have := PiLp.norm_apply_le (p := 2) (lam T ω) i
      simp only [Real.norm_eq_abs] at this
      exact le_trans this (lam_bdd hP hσ hrun T ω))
  set c1 := 2 * P.κg * P.κf / D * T with hc1def
  set c2 := 2 * Real.sqrt p * P.κg ^ 2 / D with hc2def
  set c3 := 2 * Real.sqrt p * P.νg * P.κg ^ 2 * σ / D * T with hc3def
  have hRint : Integrable (fun ω => 1 / σ * lam T ω i + c1
      + c2 * ∑ t ∈ Finset.range T, ‖lam t ω‖ + c3) μ :=
    (((hlamTint.const_mul _).add (integrable_const _)).add
      ((integrable_finsetSum _ fun t _ => hNint t).const_mul _)).add (integrable_const _)
  have hmono := integral_mono (integrable_finsetSum _ fun t _ => hGint t) hRint
    (fun ω => hc21 T i ω)
  have hR : ∫ ω, (1 / σ * lam T ω i + c1 + c2 * ∑ t ∈ Finset.range T, ‖lam t ω‖ + c3) ∂μ =
      1 / σ * ∫ ω, lam T ω i ∂μ + c1 + c2 * ∑ t ∈ Finset.range T, ∫ ω, ‖lam t ω‖ ∂μ + c3 := by
    rw [integral_add _ (integrable_const _), integral_add _ ((integrable_finsetSum _ fun t _ =>
      hNint t).const_mul _), integral_add (hlamTint.const_mul _) (integrable_const _),
      integral_const_mul, integral_const, integral_const_mul,
      integral_finsetSum _ fun t _ => hNint t, integral_const]
    · simp
    · exact (hlamTint.const_mul _).add (integrable_const _)
    · exact ((hlamTint.const_mul _).add (integrable_const _)).add
        ((integrable_finsetSum _ fun t _ => hNint t).const_mul _)
  rw [hR] at hmono
  -- bounds
  have hlamTE : ∫ ω, lam T ω i ∂μ ≤ P.κstar := by
    refine le_trans (integral_mono hlamTint (hNint T) fun ω => ?_) (hEN T)
    have := PiLp.norm_apply_le (p := 2) (lam T ω) i
    simp only [Real.norm_eq_abs] at this
    exact le_trans (le_abs_self _) this
  have hsumE : ∑ t ∈ Finset.range T, ∫ ω, ‖lam t ω‖ ∂μ ≤ T * P.κstar := by
    calc ∑ t ∈ Finset.range T, ∫ ω, ‖lam t ω‖ ∂μ ≤ ∑ t ∈ Finset.range T, P.κstar :=
          Finset.sum_le_sum fun t _ => hEN t
      _ = T * P.κstar := by simp
  have hsp := Real.sqrt_nonneg (p : ℝ)
  have hTD : (T : ℝ) / D ≤ 2 * q := by
    rw [div_le_iff₀ hD, ← hqq]
    have := mul_lt_mul_of_pos_left hDq (by positivity : (0 : ℝ) < 2 * q)
    linarith
  have hqD : q / D ≤ 2 := by
    rw [div_le_iff₀ hD]; linarith
  have b1 : 1 / σ * ∫ ω, lam T ω i ∂μ ≤ P.κstar * q := by
    rw [hσdef, one_div_one_div]
    have := mul_le_mul_of_nonneg_left hlamTE hq0.le
    linarith
  have b2 : c1 ≤ 4 * P.κg * P.κf * q := by
    have : c1 = 2 * P.κg * P.κf * (T / D) := by rw [hc1def]; ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hTD (by positivity : (0 : ℝ) ≤ 2 * P.κg * P.κf)
    linarith
  have hκs0 : 0 ≤ P.κstar := le_trans (integral_nonneg fun ω => norm_nonneg _) (hEN 0)
  have b3 : c2 * ∑ t ∈ Finset.range T, ∫ ω, ‖lam t ω‖ ∂μ ≤
      4 * Real.sqrt p * P.κstar * P.κg ^ 2 * q := by
    have hc2 : 0 ≤ c2 := by rw [hc2def]; exact div_nonneg (by positivity) hD.le
    have h1 := mul_le_mul_of_nonneg_left hsumE hc2
    have : c2 * (T * P.κstar) = 2 * Real.sqrt p * P.κg ^ 2 * P.κstar * (T / D) := by
      rw [hc2def]; ring
    rw [this] at h1
    have := mul_le_mul_of_nonneg_left hTD
      (mul_nonneg (by positivity) hκs0 : (0 : ℝ) ≤ 2 * Real.sqrt p * P.κg ^ 2 * P.κstar)
    linarith
  have b4 : c3 ≤ 4 * Real.sqrt p * P.νg * P.κg ^ 2 * q := by
    have : c3 = 2 * Real.sqrt p * P.νg * P.κg ^ 2 * (σ * T) / D := by rw [hc3def]; ring
    have hσT : σ * T = q := by rw [← hqq, ← mul_assoc, hσq, one_mul]
    rw [this, hσT, mul_div_assoc]
    have := mul_le_mul_of_nonneg_left hqD
      (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt p * P.νg * P.κg ^ 2)
    have h2 : 0 ≤ Real.sqrt p * P.νg * P.κg ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_left hq1 h2
    linarith
  unfold Problem.κc
  linarith only [hmono, b1, b2, b3, b4]
