-- Prove2me | solution 1 for PersuasionByParts.Known.quadratic_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T16:55:07.443681+00:00
-- url     : https://prove2.me/submissions/0ee40ed2-70e9-44c5-96ab-c9ba7a09f802

import Mathlib
import Definitions.Def_PersuasionByParts_Known_Pooling
import Theorems.Thm_PersuasionByParts_Known_joint_cutoff_value
import Theorems.Thm_PersuasionByParts_Known_single_cutoff_experiment
import Theorems.Thm_PersuasionByParts_Known_cutoff_reduction
import Theorems.Thm_PersuasionByParts_Known_experiment_wellposed

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known.Dev.QG
open PersuasionByParts.Known

/-- the payoff of a cutoff is the probability of the event `t ≤ posterior` -/
theorem ppay_eq {n : ℕ} (P : Prior n) (E : ProductExperiment n) (t : ℝ)
    [IsProbabilityMeasure (productSignalLaw P E)]
    (hm : Measurable (productPosterior P E)) :
    productPayoff P E (cutoff t) = (productSignalLaw P E).real {y | t ≤ productPosterior P E y} := by
  have hB : MeasurableSet {y | t ≤ productPosterior P E y} :=
    measurableSet_le measurable_const hm
  unfold productPayoff
  have : (fun y => cutoff t (productPosterior P E y)) =
      ({y | t ≤ productPosterior P E y} : Set (∀ i, E.Signal i)).indicator (fun _ => (1:ℝ)) := by
    funext y; simp [cutoff, Set.indicator_apply]
  rw [this, integral_indicator_const _ hB]; simp

theorem ppost_meas {n : ℕ} (P : Prior n) (E : ProductExperiment n) :
    Measurable (productPosterior P E) := by
  unfold productPosterior
  refine Finset.measurable_sum _ fun i _ => ?_
  have : Measurable (fun s : E.Signal i => PersuasionNetworks.posteriorMean (P.marginal i) (E.kernel i) s) :=
    (measurable_id.stronglyMeasurable.integral_kernel (κ := posterior (E.kernel i) (P.marginal i))).measurable
  exact this.comp (measurable_pi_apply i)

end PersuasionByParts.Known.Dev.QG

open PersuasionByParts.Known.Dev.QG
open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known

theorem chk_quadratic_guarantee {n : ℕ} (P : Prior n) (hn : 0 < n) (t : ℝ) (g : Decision) :
    productCutoff P t ≥ (1 / 36 : ℝ) * jointCutoff P t ^ 2 ∧
    productValue P g ≥ (1 / 144 : ℝ) * jointValue P g ^ 2 := by
  have hpart1 : ∀ t : ℝ, productCutoff P t ≥ (1 / 36 : ℝ) * jointCutoff P t ^ 2 := by
    intro t
    obtain ⟨-, -, -, hbdd, ⟨hq0, hq1⟩, ⟨hp0, hp1⟩⟩ :=
      (experiment_wellposed P hn (Decision.mk (cutoff t) (by
        unfold cutoff
        exact Measurable.ite measurableSet_Ici measurable_const measurable_const) (fun a b hab => by
        unfold cutoff
        split_ifs with h1 h2 <;>
          first | exact le_refl _ | exact absurd (le_trans h1 hab) h2 | norm_num)
        (fun y => by unfold cutoff; split_ifs <;> simp))).2.2.2.2.2.2.2.2 t
    rcases hq0.eq_or_lt with h0 | hpos
    · rw [← h0]; simp; exact hp0
    · set q := jointCutoff P t with hq
      have hqmem : q ∈ Ioc (0:ℝ) 1 := ⟨hpos, hq1⟩
      have ht : t ≤ poolMean (sumLaw P) q :=
        ((joint_cutoff_value P hn t).2.2.2 q hqmem).1 le_rfl
      have h2 := (single_cutoff_experiment P hn q t hqmem ht).2
      set E := sparseExperiment P q t
      haveI : IsProbabilityMeasure (productSignalLaw P E) := by
        unfold productSignalLaw
        haveI : ∀ i, IsProbabilityMeasure (E.kernel i ∘ₘ P.marginal i) := fun i => inferInstance
        infer_instance
      have hm := ppost_meas P E
      have hpay := ppay_eq P E t hm
      have hle : productPayoff P E (cutoff t) ≤ productCutoff P t := le_csSup hbdd ⟨E, rfl⟩
      have hsub : {s | t ≤ productPosterior P E s ∧ poolCount s ≤ 1} ⊆
          {y | t ≤ productPosterior P E y} := fun s hs => hs.1
      have hmono := measureReal_mono (μ := productSignalLaw P E) hsub
      have h2' : q ^ 2 / 36 ≤ (productSignalLaw P E).real
          {s | t ≤ productPosterior P E s ∧ poolCount s ≤ 1} := h2
      show (1 / 36 : ℝ) * q ^ 2 ≤ productCutoff P t
      linarith
  exact ⟨hpart1 t, by
    have := cutoff_reduction P hn (1/36) (by norm_num) hpart1 g
    norm_num at this ⊢
    linarith⟩

end PersuasionByParts.Known
end
end
end

theorem solution : type_of% @PersuasionByParts.Known.chk_quadratic_guarantee := @PersuasionByParts.Known.chk_quadratic_guarantee
