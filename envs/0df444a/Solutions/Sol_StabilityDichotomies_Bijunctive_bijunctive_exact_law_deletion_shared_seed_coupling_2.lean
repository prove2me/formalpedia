-- Prove2me | solution 2 for StabilityDichotomies.Bijunctive.bijunctive_exact_law_deletion_shared_seed_coupling
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:56:23.16008+00:00
-- url     : https://prove2.me/submissions/05fc74de-8180-4534-9192-2d6a56384d00

import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_deleted_seed_is_shared_priority_marginal
import Theorems.Thm_StabilityDichotomies_Solvability_wasserstein_le_measurable_seed_bit_changes
import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_output_event_measurable
import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_seed_is_probability
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (c : Constraint Γ V)
    (hc : c ∈ I.constraints) (hI : Satisfiable I) (ε : ℝ) (hε : 0 < ε)
    (A : Solver Γ) (hLaw : BijunctiveOutputLaw Γ rep ε A)
    (e : Fin I.constraints.card ≃ Option (Fin (I.delete c).constraints.card)) :
    wasserstein (A V I) (A V (I.delete c)) ≤
      ∑ v : V, (bijunctiveSeedMeasure rep I ε
        {z | bijunctiveOutput rep I ε z.1 z.2.1 z.2.2 v ≠
          bijunctiveOutput rep (I.delete c) ε (fun i => z.1 (e.symm (some i))) z.2.1 z.2.2 v}).toReal := by
  classical
  let Ω := (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ)
  let Ω' := (Fin (I.delete c).constraints.card → ℝ) × ℝ × (Literal V → ℝ)
  let μ : Measure Ω := bijunctiveSeedMeasure rep I ε
  let μ' : Measure Ω' := bijunctiveSeedMeasure rep (I.delete c) ε
  let ψ : Ω → Ω' := fun z => (fun i => z.1 (e.symm (some i)), z.2)
  let f : Ω → V → Bool := fun z => bijunctiveOutput rep I ε z.1 z.2.1 z.2.2
  let f' : Ω' → V → Bool := fun z => bijunctiveOutput rep (I.delete c) ε z.1 z.2.1 z.2.2
  let g : Ω → V → Bool := f' ∘ ψ
  haveI : IsProbabilityMeasure μ := bijunctive_seed_is_probability rep I ε hε
  haveI : IsProbabilityMeasure μ' := bijunctive_seed_is_probability rep (I.delete c) ε hε
  have hf : Measurable f := by
    apply measurable_to_countable
    intro z
    exact bijunctive_output_event_measurable rep I ε (f z)
  have hf' : Measurable f' := by
    apply measurable_to_countable
    intro z
    exact bijunctive_output_event_measurable rep (I.delete c) ε (f' z)
  have hψ : Measurable ψ := by
    apply Measurable.prodMk
    · exact measurable_pi_lambda _ fun i => (measurable_pi_apply (e.symm (some i))).comp measurable_fst
    · exact measurable_snd
  have hg : Measurable g := hf'.comp hψ
  have hμ : Measure.map ψ μ = μ' := bijunctive_deleted_seed_is_shared_priority_marginal rep I c ε hε e
  have hDel : Satisfiable (I.delete c) := by
    obtain ⟨x,hx⟩ := hI
    refine ⟨x,?_⟩
    intro d hd
    exact hx d (Multiset.mem_of_mem_erase hd)
  haveI : IsProbabilityMeasure (Measure.map f μ) := Measure.isProbabilityMeasure_map hf.aemeasurable
  haveI : IsProbabilityMeasure (Measure.map f' μ') := Measure.isProbabilityMeasure_map hf'.aemeasurable
  haveI : IsProbabilityMeasure (Measure.map g μ) := Measure.isProbabilityMeasure_map hg.aemeasurable
  have hA : A V I = (Measure.map f μ).toPMF := by
    apply PMF.ext
    intro x
    apply (ENNReal.toReal_eq_toReal_iff' ((A V I).apply_ne_top x) (((Measure.map f μ).toPMF).apply_ne_top x)).mp
    rw [Measure.toPMF_apply, Measure.map_apply hf (measurableSet_singleton x)]
    exact hLaw V I hI x
  have hA' : A V (I.delete c) = (Measure.map f' μ').toPMF := by
    apply PMF.ext
    intro x
    apply (ENNReal.toReal_eq_toReal_iff' ((A V (I.delete c)).apply_ne_top x) (((Measure.map f' μ').toPMF).apply_ne_top x)).mp
    rw [Measure.toPMF_apply, Measure.map_apply hf' (measurableSet_singleton x)]
    exact hLaw V (I.delete c) hDel x
  have hmap : Measure.map g μ = Measure.map f' μ' := by
    change Measure.map (f' ∘ ψ) μ = _
    rw [← Measure.map_map hf' hψ, hμ]
  have hB : (Measure.map g μ).toPMF = (Measure.map f' μ').toPMF := by
    apply PMF.ext
    intro x
    repeat rw [Measure.toPMF_apply]
    exact congrArg (fun q : Measure (V → Bool) => q {x}) hmap
  have hb := wasserstein_le_measurable_seed_bit_changes μ f g hf hg
  rw [← hA, hB, ← hA'] at hb
  exact hb
