-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.expected_graph_deletion_changes_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:22:25.434204+00:00
-- url     : https://prove2.me/submissions/ce87956e-645b-4fa9-a27b-8d9daa3e494e

import Theorems.Thm_StabilityDichotomies_Bijunctive_graph_deletion_change_count_le_maximum_shift
import Theorems.Thm_StabilityDichotomies_Bijunctive_score_compare_measurable
import Theorems.Thm_StabilityDichotomies_Bijunctive_finite_exponential_expected_maximum_bound
import Theorems.Thm_StabilityDichotomies_Bijunctive_finite_independent_exponential_positive_ae
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution {Γ : Language} {V : Type} [Fintype V] [Nonempty V]
    (rep : TwoCNFRepresentation Γ) (I F : Instance Γ V) (hF : Satisfiable F)
    (mask : Fin I.constraints.card → Bool) (v : V) (β : ℝ) (hβ : 0 < β) :
    let μ := Measure.pi (fun _ : Literal V => expMeasure β)
    let C := fun δ : Literal V → ℝ => ∑ j : Fin I.constraints.card,
      if decide (literalScore rep (thinnedInstance I (fun i => mask i && decide (i ≠ j))) F δ (v,false) <
        literalScore rep (thinnedInstance I (fun i => mask i && decide (i ≠ j))) F δ (v,true)) ≠
          decide (literalScore rep (thinnedInstance I mask) F δ (v,false) <
            literalScore rep (thinnedInstance I mask) F δ (v,true)) then (1 : ℝ) else 0
    Integrable C μ ∧ (∫ δ, C δ ∂μ) ≤ (Real.log (Fintype.card (Literal V)) + 1) / β := by
  classical
  let μ : Measure (Literal V → ℝ) := Measure.pi (fun _ => expMeasure β)
  let G := thinnedInstance I mask
  let Gdel := fun j : Fin I.constraints.card => thinnedInstance I (fun i => mask i && decide (i ≠ j))
  let bit := fun (H : Instance Γ V) (δ : Literal V → ℝ) =>
    decide (literalScore rep H F δ (v,false) < literalScore rep H F δ (v,true))
  let C : (Literal V → ℝ) → ℝ := fun δ => ∑ j : Fin I.constraints.card,
    if bit (Gdel j) δ ≠ bit G δ then 1 else 0
  let M : (Literal V → ℝ) → ℝ := fun δ => max 0 (Finset.univ.sup' Finset.univ_nonempty δ)
  have hb (H : Instance Γ V) : MeasurableSet {δ : Literal V → ℝ | bit H δ = true} := by
    have h := score_compare_measurable rep H F (v,true) (v,false)
    simpa [bit] using h
  have hchange (j : Fin I.constraints.card) : MeasurableSet {δ | bit (Gdel j) δ ≠ bit G δ} := by
    have hs : {δ | bit (Gdel j) δ ≠ bit G δ} =
      ({δ | bit (Gdel j) δ = true} ∩ {δ | bit G δ = true}ᶜ) ∪
      ({δ | bit (Gdel j) δ = true}ᶜ ∩ {δ | bit G δ = true}) := by
      ext δ
      cases h1 : bit (Gdel j) δ <;> cases h2 : bit G δ <;> simp [h1,h2]
    rw [hs]
    exact ((hb _).inter (hb _).compl).union ((hb _).compl.inter (hb _))
  have hCmeas : Measurable C := by
    apply Finset.measurable_sum
    intro j hj
    exact Measurable.ite (hchange j) measurable_const measurable_const
  have hCnonneg (δ : Literal V → ℝ) : 0 ≤ C δ := by
    apply Finset.sum_nonneg
    intro j hj
    split_ifs <;> norm_num
  have hmax := finite_exponential_expected_maximum_bound (α := Literal V) β hβ
  have hMn : Integrable M μ := hmax.1
  have hbound : ∀ᵐ δ ∂μ, C δ ≤ M δ := by
    filter_upwards [finite_independent_exponential_positive_ae (α := Literal V) β hβ] with δ hδ
    have hc := graph_deletion_change_count_le_maximum_shift rep I F hF mask δ hδ v
    change (∑ j : Fin I.constraints.card, if bit (Gdel j) δ ≠ bit G δ then (1 : ℝ) else 0) ≤ M δ
    rw [Finset.sum_boole]
    exact hc
  have hCi : Integrable C μ := by
    apply hMn.mono' hCmeas.aestronglyMeasurable
    filter_upwards [hbound] with δ hδ
    rwa [Real.norm_eq_abs,abs_of_nonneg (hCnonneg δ)]
  have hh := integral_mono_ae hCi hMn hbound
  exact ⟨hCi,hh.trans hmax.2⟩
