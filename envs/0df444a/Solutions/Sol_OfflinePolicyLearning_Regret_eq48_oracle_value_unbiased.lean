-- Prove2me | solution 1 for OfflinePolicyLearning.Regret.eq48_oracle_value_unbiased
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T23:39:26.609383+00:00
-- url     : https://prove2.me/submissions/2eba9ccb-06bb-44f9-a800-edd86799d703

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Regret_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open OfflinePolicyLearning.Regret
theorem opl_law_prob {X : Type*} [MeasurableSpace X] {d : ℕ} (M : Model X d) :
    IsProbabilityMeasure M.law := by
  unfold Model.law; infer_instance

/-- The outcome vector is a.s. bounded by `|B|` under the joint law. -/
theorem opl_law_bound {X : Type*} [MeasurableSpace X] {d : ℕ} (M : Model X d)
    (B : ℝ) (hB : ∀ x, ∀ᵐ y ∂(M.κY x), ∀ a, |y a| ≤ B) :
    ∀ᵐ ω ∂M.law, ∀ a, |ω.2.1 a| ≤ |B| := by
  have hmeasS : MeasurableSet {ω : Draw X d | ∀ a, |ω.2.1 a| ≤ |B|} := by
    have : {ω : Draw X d | ∀ a, |ω.2.1 a| ≤ |B|} = ⋂ a, {ω : Draw X d | |ω.2.1 a| ≤ |B|} := by
      ext ω; simp
    rw [this]
    refine MeasurableSet.iInter fun a => measurableSet_le ?_ measurable_const
    exact ((measurable_pi_apply a).comp (measurable_fst.comp measurable_snd)).abs
  unfold Model.law
  refine Measure.ae_compProd_of_ae_ae hmeasS (Filter.Eventually.of_forall fun x => ?_)
  rw [Kernel.prod_apply]
  exact (Measure.quasiMeasurePreserving_fst).ae
    ((hB x).mono fun y hy a => (hy a).trans (le_abs_self B))

theorem opl_mu_bound {X : Type*} [MeasurableSpace X] {d : ℕ} (M : Model X d)
    (B : ℝ) (hB : ∀ x, ∀ᵐ y ∂(M.κY x), ∀ a, |y a| ≤ B) (x : X) (a : Fin d) :
    |M.μ x a| ≤ |B| := by
  have := norm_integral_le_of_norm_le_const (μ := M.κY x) (C := |B|)
    (f := fun y : Fin d → ℝ => y a) ((hB x).mono fun y hy => by
      simpa using (hy a).trans (le_abs_self B))
  simpa [Model.μ, probReal_univ] using this

theorem opl_Gamma_measurable {X : Type*} [MeasurableSpace X] {d : ℕ} (M : Model X d)
    (π : X → Fin d) (hπ : Measurable π) :
    Measurable fun ω : Draw X d => M.Γ (obs ω) (π ω.1) := by
  have hμm : ∀ j, Measurable fun x => M.μ x j := fun j =>
    (StronglyMeasurable.integral_kernel (κ := M.κY) (f := fun y : Fin d → ℝ => y j)
      (measurable_pi_apply j).stronglyMeasurable).measurable
  have hem : ∀ j, Measurable fun x => M.e x j := fun j =>
    (M.κA.measurable_coe (measurableSet_singleton j)).ennreal_toReal
  let H : Draw X d × (Fin d × Fin d) → ℝ := fun p =>
    M.μ p.1.1 p.2.2 + if p.2.1 = p.2.2 then (p.1.2.1 p.2.1 - M.μ p.1.1 p.2.1) / M.e p.1.1 p.2.1
      else 0
  have hH : Measurable H := by
    refine measurable_from_prod_countable_left fun y => ?_
    dsimp only [H]
    by_cases h : y.1 = y.2
    · simp only [h, if_true]
      exact ((hμm _).comp measurable_fst).add
        ((((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)).sub
          ((hμm _).comp measurable_fst)).div ((hem _).comp measurable_fst))
    · simp only [h, if_false, add_zero]
      exact (hμm _).comp measurable_fst
  have : (fun ω : Draw X d => M.Γ (obs ω) (π ω.1)) =
      H ∘ fun ω => (ω, (ω.2.2, π ω.1)) := rfl
  rw [this]
  exact hH.comp (measurable_id.prodMk
    ((measurable_snd.comp measurable_snd).prodMk (hπ.comp measurable_fst)))

theorem opl_Gamma_bound {X : Type*} [MeasurableSpace X] {d : ℕ} (M : Model X d)
    (η : ℝ) (hη : 0 < η) (hover : ∀ x a, η ≤ M.e x a)
    (B : ℝ) (hB : ∀ x, ∀ᵐ y ∂(M.κY x), ∀ a, |y a| ≤ B) :
    ∀ᵐ ω ∂M.law, ∀ j, |M.Γ (obs ω) j| ≤ |B| + 2 * |B| / η := by
  filter_upwards [opl_law_bound M B hB] with ω hω j
  change |M.μ ω.1 j + (if ω.2.2 = j then (ω.2.1 ω.2.2 - M.μ ω.1 ω.2.2) / M.e ω.1 ω.2.2 else 0)|
    ≤ |B| + 2 * |B| / η
  have h1 := opl_mu_bound M B hB ω.1 j
  by_cases h : ω.2.2 = j
  · rw [if_pos h]
    have h2 := opl_mu_bound M B hB ω.1 ω.2.2
    have h3 := hω ω.2.2
    have he := hover ω.1 ω.2.2
    have hepos : 0 < M.e ω.1 ω.2.2 := lt_of_lt_of_le hη he
    have hq : |(ω.2.1 ω.2.2 - M.μ ω.1 ω.2.2) / M.e ω.1 ω.2.2| ≤ 2 * |B| / η := by
      rw [abs_div, abs_of_pos hepos]
      have hnum : |ω.2.1 ω.2.2 - M.μ ω.1 ω.2.2| ≤ 2 * |B| := by
        calc _ ≤ |ω.2.1 ω.2.2| + |M.μ ω.1 ω.2.2| := abs_sub _ _
          _ ≤ 2 * |B| := by linarith
      calc _ ≤ 2 * |B| / M.e ω.1 ω.2.2 := by gcongr
        _ ≤ 2 * |B| / η := by gcongr
    calc _ ≤ |M.μ ω.1 j| + |(ω.2.1 ω.2.2 - M.μ ω.1 ω.2.2) / M.e ω.1 ω.2.2| := abs_add_le _ _
      _ ≤ _ := by linarith
  · rw [if_neg h, add_zero]
    have : 0 ≤ 2 * |B| / η := by positivity
    linarith

theorem solution {X : Type*} [MeasurableSpace X] {d : ℕ} (M : Model X d)
    (η : ℝ) (hη : 0 < η) (hover : ∀ x a, η ≤ M.e x a)
    (B : ℝ) (hB : ∀ x, ∀ᵐ y ∂(M.κY x), ∀ a, |y a| ≤ B)
    (π : X → Fin d) (hπ : Measurable π) (n : ℕ) (hn : 1 ≤ n) :
    ∫ D, M.Qtilde D π ∂M.sample n = M.Q π := by
  have hprob := opl_law_prob M
  set g : Draw X d → ℝ := fun ω => M.Γ (obs ω) (π ω.1) with hg
  have hgm : Measurable g := opl_Gamma_measurable M π hπ
  have hgint : Integrable g M.law :=
    Integrable.of_bound hgm.aestronglyMeasurable (|B| + 2 * |B| / η)
      ((opl_Gamma_bound M η hη hover B hB).mono fun ω h => by
        rw [Real.norm_eq_abs]; exact h _)
  set f : Draw X d → ℝ := fun ω => ω.2.1 (π ω.1) with hf
  have hfm : Measurable f := by
    have : f = (fun p : Draw X d × Fin d => p.1.2.1 p.2) ∘ fun ω => (ω, π ω.1) := rfl
    rw [this]
    refine Measurable.comp ?_ (measurable_id.prodMk (hπ.comp measurable_fst))
    exact measurable_from_prod_countable_left fun j =>
      (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
  have hfint : Integrable f M.law :=
    Integrable.of_bound hfm.aestronglyMeasurable |B|
      ((opl_law_bound M B hB).mono fun ω h => by rw [Real.norm_eq_abs]; exact h _)
  -- Step 1: the oracle score is unbiased for the reward of the policy under the joint law
  have hone : ∫ ω, g ω ∂M.law = M.Q π := by
    have hdiff : ∫ ω, (g ω - f ω) ∂M.law = 0 := by
      have hsub : Integrable (fun ω => g ω - f ω) M.law := hgint.sub hfint
      unfold Model.law at hsub ⊢
      rw [Measure.integral_compProd hsub]
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.zero_apply]
      rw [Kernel.prod_apply]
      have hpt : ∀ p : (Fin d → ℝ) × Fin d, g (x, p) - f (x, p) =
          (p.1 (π x) - M.μ x (π x)) *
            ((if p.2 = π x then 1 else 0) / M.e x (π x) - 1) := by
        rintro ⟨y, a⟩
        simp only [hg, hf]
        change M.μ x (π x) + (if a = π x then (y a - M.μ x a) / M.e x a else 0) - y (π x) = _
        by_cases h : a = π x
        · subst h; simp only [if_true]; ring
        · simp only [h, if_false]; ring
      simp_rw [hpt]
      rw [integral_prod_mul (f := fun y : Fin d → ℝ => y (π x) - M.μ x (π x))
        (g := fun a : Fin d => (if a = π x then (1 : ℝ) else 0) / M.e x (π x) - 1)]
      have hyint : Integrable (fun y : Fin d → ℝ => y (π x)) (M.κY x) :=
        Integrable.of_bound (measurable_pi_apply (π x)).aestronglyMeasurable B
          ((hB x).mono fun y h => by rw [Real.norm_eq_abs]; exact h _)
      have : ∫ y, (y (π x) - M.μ x (π x)) ∂(M.κY x) = 0 := by
        rw [integral_sub hyint (integrable_const _), integral_const]
        simp [Model.μ, probReal_univ]
      rw [this, zero_mul]
    rw [integral_sub hgint hfint, sub_eq_zero] at hdiff
    rw [hdiff]
    rfl
  -- Step 2: average over the iid sample
  have hcoord : ∀ i : Fin n, ∫ D, g (D i) ∂M.sample n = ∫ ω, g ω ∂M.law := by
    intro i
    have hmp := measurePreserving_eval (fun _ : Fin n => M.law) i
    unfold Model.sample
    rw [← integral_map (measurable_pi_apply i).aemeasurable
      (by rw [hmp.map_eq]; exact hgm.aestronglyMeasurable), hmp.map_eq]
  have hcint : ∀ i : Fin n, Integrable (fun D : Fin n → Draw X d => g (D i)) (M.sample n) := by
    intro i
    have hmp := measurePreserving_eval (fun _ : Fin n => M.law) i
    unfold Model.sample
    exact Integrable.comp_measurable (by rw [hmp.map_eq]; exact hgint) (measurable_pi_apply i)
  have hnpos : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact this.ne'
  unfold Model.Qtilde
  rw [integral_const_mul, integral_finsetSum _ fun i _ => hcint i]
  simp only [hg] at hcoord ⊢
  rw [Finset.sum_congr rfl fun i _ => hcoord i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, hone]
  field_simp
