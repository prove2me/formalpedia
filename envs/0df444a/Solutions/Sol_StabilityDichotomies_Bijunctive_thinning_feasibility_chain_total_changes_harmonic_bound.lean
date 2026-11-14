-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.thinning_feasibility_chain_total_changes_harmonic_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:02:58.317208+00:00
-- url     : https://prove2.me/submissions/f580364a-88a2-45ff-9a77-caadc7f1d049

import Theorems.Thm_StabilityDichotomies_Bijunctive_fixed_feasibility_chain_total_changes_harmonic_bound
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem thinned_member {Γ : Language} {V : Type} (I : Instance Γ V)
    (mask : Fin I.constraints.card → Bool) (c : Constraint Γ V)
    (hc : c ∈ (thinnedInstance I mask).constraints) : c ∈ I.constraints := by
  simp only [thinnedInstance, Multiset.mem_coe, List.mem_map, List.mem_filter, List.mem_ofFn] at hc
  obtain ⟨⟨i, d⟩, ⟨⟨j, hj⟩, hm⟩, hd⟩ := hc
  cases hj
  simp only [Prod.snd] at hd
  subst c
  simp only [occurrenceAt]
  exact Multiset.mem_toList.mp (List.get_mem _ _)

private theorem thinned_mask_mono {Γ : Language} {V : Type} (I : Instance Γ V)
    (small big : Fin I.constraints.card → Bool)
    (h : ∀ i, small i = true → big i = true) :
    ∀ c, c ∈ (thinnedInstance I small).constraints → c ∈ (thinnedInstance I big).constraints := by
  intro c hc
  simp only [thinnedInstance, Multiset.mem_coe, List.mem_map, List.mem_filter, List.mem_ofFn] at hc ⊢
  obtain ⟨⟨i, d⟩, ⟨⟨j, hj⟩, hm⟩, hd⟩ := hc
  refine ⟨(i,d), ⟨⟨j,hj⟩, ?_⟩, hd⟩
  exact h i hm

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I)
    (m : ℕ → Fin I.constraints.card → Bool) (k : ℕ)
    (hbase : ∀ i ≤ k, ∀ j, m 0 j = true → m i j = true)
    (hchain : ∀ i < k, ∀ j, m i j = true → m (i+1) j = true)
    (β : ℝ) (hβ : 0 < β) :
    (∑ i ∈ Finset.range k, ∑ v : V,
      (Measure.pi (fun _ : Literal V => expMeasure β)
        {δ : Literal V → ℝ |
          decide (literalScore rep (thinnedInstance I (m 0)) (thinnedInstance I (m i)) δ (v,false) <
            literalScore rep (thinnedInstance I (m 0)) (thinnedInstance I (m i)) δ (v,true)) ≠
          decide (literalScore rep (thinnedInstance I (m 0)) (thinnedInstance I (m (i+1))) δ (v,false) <
            literalScore rep (thinnedInstance I (m 0)) (thinnedInstance I (m (i+1))) δ (v,true))}).toReal) ≤
      (maxArity Γ * I.constraints.card : ℕ) * (harmonic (Fintype.card (Literal V)) : ℝ) := by
  apply fixed_feasibility_chain_total_changes_harmonic_bound rep I (thinnedInstance I (m 0)) hI
    (fun i => thinnedInstance I (m i)) k
  · exact fun _ hc => hc
  · intro i hi
    exact thinned_mask_mono I (m 0) (m i) (hbase i hi)
  · intro i hi c hc
    exact thinned_member I (m i) c hc
  · intro i hi
    exact thinned_mask_mono I (m i) (m (i+1)) (hchain i hi)
  · exact hβ
