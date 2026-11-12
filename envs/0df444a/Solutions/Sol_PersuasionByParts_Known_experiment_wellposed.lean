-- Prove2me | solution 1 for PersuasionByParts.Known.experiment_wellposed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T16:55:05.84678+00:00
-- url     : https://prove2.me/submissions/4da9fb57-2b55-4b00-b5d1-51b3e32a2ac1

import Mathlib
import Definitions.Def_PersuasionByParts_Known_Model

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
noncomputable section

namespace PersuasionByParts.Known.Dev.Post

variable {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧] [StandardBorelSpace Ω]
  [Nonempty Ω] (κ : Kernel Ω 𝓧) [IsMarkovKernel κ] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- integrability of the joint test function `1_B(s) f(x)` against the posterior-joint law -/
private theorem integrable_joint (f : Ω → ℝ) (hfm : Measurable f) (hf : Integrable f μ)
    {B : Set 𝓧} (hB : MeasurableSet B) :
    Integrable (fun p : 𝓧 × Ω => B.indicator (fun _ => (1:ℝ)) p.1 * f p.2)
      ((κ ∘ₘ μ) ⊗ₘ κ†μ) := by
  rw [compProd_posterior_eq_map_swap]
  have hm : Measurable (fun p : 𝓧 × Ω => B.indicator (fun _ => (1:ℝ)) p.1 * f p.2) :=
    ((measurable_const.indicator hB).comp measurable_fst).mul (hfm.comp measurable_snd)
  rw [integrable_map_measure hm.aestronglyMeasurable measurable_swap.aemeasurable]
  have h1 : Integrable (fun p : Ω × 𝓧 => f p.1) (μ ⊗ₘ κ) := by
    have hmap : (μ ⊗ₘ κ).map Prod.fst = μ := Measure.fst_compProd μ κ
    have h0 : Integrable f ((μ ⊗ₘ κ).map Prod.fst) := by rw [hmap]; exact hf
    exact (integrable_map_measure (by rw [hmap]; exact hfm.aestronglyMeasurable)
      measurable_fst.aemeasurable).1 h0
  refine h1.norm.mono' ?_ (Eventually.of_forall fun p => ?_)
  · exact (hm.comp measurable_swap).aestronglyMeasurable
  · simp only [Function.comp, Prod.fst_swap, Prod.snd_swap, Real.norm_eq_abs, abs_mul]
    by_cases h : p.2 ∈ B <;> simp [h, Real.norm_eq_abs]

theorem integrable_posterior_integral (f : Ω → ℝ) (hfm : Measurable f) (hf : Integrable f μ) :
    Integrable (fun s => ∫ x, f x ∂(κ†μ) s) (κ ∘ₘ μ) := by
  have h := integrable_joint κ μ f hfm hf (B := Set.univ) MeasurableSet.univ
  simp only [indicator_univ] at h
  have h2 := h.integral_compProd
  simpa [one_mul] using h2

end PersuasionByParts.Known.Dev.Post
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known.Dev.WP
open PersuasionByParts.Known

theorem total_meas {n : ℕ} : Measurable (total : (Fin n → ℝ) → ℝ) := by
  unfold total; fun_prop

theorem integrable_total {n : ℕ} (P : Prior n) :
    Integrable (total : (Fin n → ℝ) → ℝ) (priorLaw P) := by
  have : (total : (Fin n → ℝ) → ℝ) = fun x => ∑ i, x i := rfl
  rw [this]
  refine integrable_finsetSum _ fun i _ => ?_
  have h0 : Integrable id ((priorLaw P).map (Function.eval i)) := by
    rw [priorLaw, (measurePreserving_eval P.marginal i).map_eq]; exact P.finiteMean i
  exact (integrable_map_measure aestronglyMeasurable_id (measurable_pi_apply i).aemeasurable).1 h0

instance instJ {n : ℕ} (P : Prior n) (E : JointExperiment n) :
    IsProbabilityMeasure (jointSignalLaw P E) := by
  unfold jointSignalLaw; infer_instance

instance instPr {n : ℕ} (P : Prior n) (E : ProductExperiment n) :
    IsProbabilityMeasure (productSignalLaw P E) := by
  unfold productSignalLaw
  haveI : ∀ i, IsProbabilityMeasure (E.kernel i ∘ₘ P.marginal i) := fun i => inferInstance
  infer_instance

theorem jpost_meas {n : ℕ} (P : Prior n) (E : JointExperiment n) :
    Measurable (jointPosterior P E) :=
  ((total_meas (n := n)).stronglyMeasurable.integral_kernel).measurable

theorem jpost_int {n : ℕ} (P : Prior n) (E : JointExperiment n) :
    Integrable (jointPosterior P E) (jointSignalLaw P E) :=
  Post.integrable_posterior_integral E.kernel (priorLaw P) total total_meas (integrable_total P)

theorem ppost_meas {n : ℕ} (P : Prior n) (E : ProductExperiment n) :
    Measurable (productPosterior P E) := by
  unfold productPosterior
  refine Finset.measurable_sum _ fun i _ => ?_
  have : Measurable (fun s : E.Signal i => PersuasionNetworks.posteriorMean (P.marginal i) (E.kernel i) s) :=
    (measurable_id.stronglyMeasurable.integral_kernel (κ := posterior (E.kernel i) (P.marginal i))).measurable
  exact this.comp (measurable_pi_apply i)

theorem ppost_int {n : ℕ} (P : Prior n) (E : ProductExperiment n) :
    Integrable (productPosterior P E) (productSignalLaw P E) := by
  unfold productPosterior
  refine integrable_finsetSum _ fun i _ => ?_
  have h1 : Integrable (fun s : E.Signal i => PersuasionNetworks.posteriorMean (P.marginal i) (E.kernel i) s)
      (E.kernel i ∘ₘ P.marginal i) :=
    Post.integrable_posterior_integral (E.kernel i) (P.marginal i) id measurable_id (P.finiteMean i)
  haveI : ∀ j, IsProbabilityMeasure (E.kernel j ∘ₘ P.marginal j) := fun j => inferInstance
  exact (measurePreserving_eval (fun j => E.kernel j ∘ₘ P.marginal j) i).integrable_comp_of_integrable h1

theorem int01 {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (f : α → ℝ) (hf : Measurable f) (h01 : ∀ y, f y ∈ Icc (0:ℝ) 1) :
    Integrable f ν ∧ ∫ y, f y ∂ν ∈ Icc (0:ℝ) 1 := by
  have hi : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [(h01 x).1], (h01 x).2⟩)
  refine ⟨hi, integral_nonneg fun y => (h01 y).1, ?_⟩
  calc ∫ y, f y ∂ν ≤ ∫ _y, (1:ℝ) ∂ν := integral_mono hi (integrable_const _) fun y => (h01 y).2
    _ = 1 := by simp

theorem sSup_facts (S : Set ℝ) (hne : S.Nonempty) (h : ∀ v ∈ S, v ∈ Icc (0:ℝ) 1) :
    BddAbove S ∧ sSup S ∈ Icc (0:ℝ) 1 := by
  have hb : BddAbove S := ⟨1, fun v hv => (h v hv).2⟩
  obtain ⟨v, hv⟩ := hne
  exact ⟨hb, le_trans (h v hv).1 (le_csSup hb hv), csSup_le ⟨v, hv⟩ fun w hw => (h w hw).2⟩

theorem facts {n : ℕ} (P : Prior n) (g : ℝ → ℝ) (hg : Measurable g)
    (h01 : ∀ y, g y ∈ Icc (0:ℝ) 1) :
    (jointPayoffs P g).Nonempty ∧ BddAbove (jointPayoffs P g) ∧
    (productPayoffs P g).Nonempty ∧ BddAbove (productPayoffs P g) ∧
    jointValue P g ∈ Icc 0 1 ∧ productValue P g ∈ Icc 0 1 ∧
    (∀ E : JointExperiment n,
      Integrable (fun s => g (jointPosterior P E s)) (jointSignalLaw P E) ∧
      jointPayoff P E g ∈ Icc 0 1) ∧
    (∀ E : ProductExperiment n,
      Integrable (fun s => g (productPosterior P E s)) (productSignalLaw P E) ∧
      productPayoff P E g ∈ Icc 0 1) := by
  have hJ : ∀ E : JointExperiment n,
      Integrable (fun s => g (jointPosterior P E s)) (jointSignalLaw P E) ∧
      jointPayoff P E g ∈ Icc 0 1 := fun E =>
    int01 _ _ (hg.comp (jpost_meas P E)) fun y => h01 _
  have hP : ∀ E : ProductExperiment n,
      Integrable (fun s => g (productPosterior P E s)) (productSignalLaw P E) ∧
      productPayoff P E g ∈ Icc 0 1 := fun E =>
    int01 _ _ (hg.comp (ppost_meas P E)) fun y => h01 _
  have hJne : (jointPayoffs P g).Nonempty := ⟨_, jointRevelation n, rfl⟩
  have hPne : (productPayoffs P g).Nonempty := ⟨_, productRevelation n, rfl⟩
  have hJs := sSup_facts (jointPayoffs P g) hJne (by
    rintro v ⟨E, rfl⟩; exact (hJ E).2)
  have hPs := sSup_facts (productPayoffs P g) hPne (by
    rintro v ⟨E, rfl⟩; exact (hP E).2)
  exact ⟨hJne, hJs.1, hPne, hPs.1, hJs.2, hPs.2, hJ, hP⟩

end PersuasionByParts.Known.Dev.WP

open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known
open PersuasionByParts.Known.Dev.WP

theorem chk_experiment_wellposed {n : ℕ} (P : Prior n) (hn : 0 < n) (g : Decision) :
    (jointPayoffs P g).Nonempty ∧ BddAbove (jointPayoffs P g) ∧
    (productPayoffs P g).Nonempty ∧ BddAbove (productPayoffs P g) ∧
    jointValue P g ∈ Icc 0 1 ∧ productValue P g ∈ Icc 0 1 ∧
    (∀ E : JointExperiment n,
      Integrable (jointPosterior P E) (jointSignalLaw P E) ∧
      Integrable (fun s => g (jointPosterior P E s)) (jointSignalLaw P E) ∧
      jointPayoff P E g ∈ Icc 0 1) ∧
    (∀ E : ProductExperiment n,
      Integrable (productPosterior P E) (productSignalLaw P E) ∧
      Integrable (fun s => g (productPosterior P E s)) (productSignalLaw P E) ∧
      productPayoff P E g ∈ Icc 0 1) ∧
    (∀ t : ℝ,
      (jointPayoffs P (cutoff t)).Nonempty ∧ BddAbove (jointPayoffs P (cutoff t)) ∧
      (productPayoffs P (cutoff t)).Nonempty ∧ BddAbove (productPayoffs P (cutoff t)) ∧
      jointCutoff P t ∈ Icc 0 1 ∧ productCutoff P t ∈ Icc 0 1) := by
  have hc : ∀ t : ℝ, Measurable (cutoff t) := fun t => by
    unfold cutoff
    exact Measurable.ite measurableSet_Ici measurable_const measurable_const
  have hc01 : ∀ t y : ℝ, cutoff t y ∈ Icc (0:ℝ) 1 := fun t y => by
    unfold cutoff; split_ifs <;> simp
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := facts P g g.measurable g.range
  refine ⟨a1, a2, a3, a4, a5, a6, fun E => ⟨jpost_int P E, (a7 E)⟩, fun E => ⟨ppost_int P E, (a8 E)⟩,
    fun t => ?_⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, -, -⟩ := facts P (cutoff t) (hc t) (hc01 t)
  exact ⟨b1, b2, b3, b4, b5, b6⟩

end PersuasionByParts.Known
end
end
end

theorem solution : type_of% @PersuasionByParts.Known.chk_experiment_wellposed := @PersuasionByParts.Known.chk_experiment_wellposed
