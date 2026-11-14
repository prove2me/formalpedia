-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.total_graph_deletion_bit_change_probabilities_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:50:07.318166+00:00
-- url     : https://prove2.me/submissions/9a5aa492-25e3-460b-8295-18a226fdf364

import Theorems.Thm_StabilityDichotomies_Bijunctive_expected_total_seed_graph_deletion_changes_bound
import Theorems.Thm_StabilityDichotomies_Bijunctive_graph_deleted_bit_event_measurable
import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_output_event_measurable
import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_seed_is_probability
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution {Γ : Language} {V : Type} [Fintype V] [Nonempty V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I) (ε : ℝ) (hε : 0 < ε) :
    let μ := bijunctiveSeedMeasure rep I ε
    let mid := fun (j : Fin I.constraints.card) (z : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ)) v =>
      decide (literalScore rep (thinnedInstance I (fun i => decide (z.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
          (thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1))) z.2.2 (v,false) <
        literalScore rep (thinnedInstance I (fun i => decide (z.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
          (thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1))) z.2.2 (v,true))
    (∑ j : Fin I.constraints.card, ∑ v : V,
      (μ {z | bijunctiveOutput rep I ε z.1 z.2.1 z.2.2 v ≠ mid j z v}).toReal) ≤
    (maxArity Γ * I.constraints.card : ℕ) *
      ((Real.log (Fintype.card (Literal V)) + 1) / bijunctiveRate rep ε) := by
  classical
  let Ω := (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ)
  let μ : Measure Ω := bijunctiveSeedMeasure rep I ε
  let mid := fun (j : Fin I.constraints.card) (z : Ω) v =>
      decide (literalScore rep (thinnedInstance I (fun i => decide (z.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
          (thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1))) z.2.2 (v,false) <
        literalScore rep (thinnedInstance I (fun i => decide (z.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
          (thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1))) z.2.2 (v,true))
  let out : Ω → V → Bool := fun z => bijunctiveOutput rep I ε z.1 z.2.1 z.2.2
  let E := fun (j : Fin I.constraints.card) (v : V) => {z : Ω | mid j z v ≠ out z v}
  haveI : IsProbabilityMeasure μ := bijunctive_seed_is_probability rep I ε hε
  have hout : Measurable out := by
    apply measurable_to_countable
    intro z
    exact bijunctive_output_event_measurable rep I ε (out z)
  have hmid (j : Fin I.constraints.card) (v : V) : Measurable (fun z => mid j z v) := by
    have h := graph_deleted_bit_event_measurable rep I ε j v
    simpa [mid] using (Measurable.ite h measurable_const measurable_const :
      Measurable (fun z : Ω => if literalScore rep (thinnedInstance I (fun i => decide (z.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
          (thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1))) z.2.2 (v,false) <
        literalScore rep (thinnedInstance I (fun i => decide (z.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
          (thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1))) z.2.2 (v,true) then true else false))
  have hE (j : Fin I.constraints.card) (v : V) : MeasurableSet (E j v) :=
    (measurableSet_eq_fun (hmid j v) ((measurable_pi_apply v).comp hout)).compl
  let f : Fin I.constraints.card → V → Ω → ℝ := fun j v => (E j v).indicator 1
  have hInt (j : Fin I.constraints.card) (v : V) : Integrable (f j v) μ :=
    (integrable_const (1 : ℝ)).indicator (hE j v)
  have hEq : (∫ z, ∑ v : V, ∑ j : Fin I.constraints.card, f j v z ∂μ) =
      ∑ j : Fin I.constraints.card, ∑ v : V, μ.real (E j v) := by
    rw [integral_finset_sum _ (fun v _ => integrable_finset_sum _ (fun j _ => hInt j v))]
    simp_rw [integral_finset_sum _ (fun j _ => hInt j _)]
    simp_rw [f, integral_indicator_one (hE _ _)]
    rw [Finset.sum_comm]
  have hb := (expected_total_seed_graph_deletion_changes_bound rep I hI ε hε).2
  have hh : (fun z : Ω => ∑ v : V, ∑ j : Fin I.constraints.card, f j v z) =
      (fun z : Ω => ∑ v : V, ∑ j : Fin I.constraints.card,
        if mid j z v ≠ out z v then (1 : ℝ) else 0) := by
    funext z
    simp [f,E,Set.indicator_apply]
  rw [← hh, hEq] at hb
  change (∑ j : Fin I.constraints.card, ∑ v : V, μ.real {z | out z v ≠ mid j z v}) ≤ _
  convert hb using 1
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro v hv
  congr 1
  ext z
  simp [E,ne_comm]
