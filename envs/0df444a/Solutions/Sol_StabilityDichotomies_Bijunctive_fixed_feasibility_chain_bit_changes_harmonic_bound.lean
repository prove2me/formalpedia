-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.fixed_feasibility_chain_bit_changes_harmonic_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:10:37.815428+00:00
-- url     : https://prove2.me/submissions/b6499a85-8a9e-4e8a-a9e5-9dea8d3e54e0

import Theorems.Thm_StabilityDichotomies_Bijunctive_feasible_root_candidate_encoding
import Theorems.Thm_StabilityDichotomies_Bijunctive_shifted_exponential_nested_positive_changes_le_harmonic
import Theorems.Thm_StabilityDichotomies_Bijunctive_finite_shifted_exponential_scores_pairwise_distinct_ae
import Theorems.Thm_StabilityDichotomies_Bijunctive_finite_independent_exponential_positive_ae
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem harmonic_real_mono {m n : ℕ} (hmn : m ≤ n) : (harmonic m : ℝ) ≤ harmonic n := by
  simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
  intro i hi hnot
  positivity

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I G : Instance Γ V) (hI : Satisfiable I)
    (F : ℕ → Instance Γ V) (k : ℕ) (v : V)
    (hG : ∀ c ∈ G.constraints, c ∈ (F 0).constraints)
    (hbase : ∀ i ≤ k, ∀ c ∈ (F 0).constraints, c ∈ (F i).constraints)
    (hIcontains : ∀ i ≤ k, ∀ c ∈ (F i).constraints, c ∈ I.constraints)
    (hchain : ∀ i < k, ∀ c ∈ (F i).constraints, c ∈ (F (i+1)).constraints)
    (β : ℝ) (hβ : 0 < β) :
    (∑ i ∈ Finset.range k,
      (Measure.pi (fun _ : Literal V => expMeasure β)
        {δ : Literal V → ℝ |
          decide (literalScore rep G (F i) δ (v,false) < literalScore rep G (F i) δ (v,true)) ≠
          decide (literalScore rep G (F (i+1)) δ (v,false) < literalScore rep G (F (i+1)) δ (v,true))}).toReal) ≤
      (harmonic (Fintype.card (Literal V)) : ℝ) := by
  classical
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  let μ : Measure (Literal V → ℝ) := Measure.pi (fun _ => expMeasure β)
  haveI : IsProbabilityMeasure μ := by unfold μ; infer_instance
  obtain ⟨C,label,d,hdC,henc⟩ := feasible_root_candidate_encoding rep G (F 0) v hG
  let d' : Literal V → ℝ := fun r => if r ∈ C then d r else 0
  have hd' (r : Literal V) : 0 ≤ d' r := by
    by_cases h : r ∈ C
    · simp [d',h,hdC r h]
    · simp [d',h]
  let sets : ℕ → Finset (Literal V) := fun i => C.filter (fun r => feasibleLiteral (F i) r)
  have hsets (i : ℕ) (r : Literal V) : r ∈ sets i ↔ r ∈ C ∧ feasibleLiteral (F i) r := by simp [sets]
  have hnested : ∀ i < k, sets (i+1) ⊆ sets i := by
    intro i hi r hr
    obtain ⟨hrC,hrF⟩ := (hsets (i+1) r).mp hr
    obtain ⟨x,hx,hxr⟩ := hrF
    refine (hsets i r).mpr ⟨hrC, x, ?_, hxr⟩
    intro c hc
    exact hx c (hchain i hi c hc)
  have hsat (i : ℕ) (hi : i ≤ k) : Satisfiable (F i) := by
    obtain ⟨x,hx⟩ := hI
    exact ⟨x,fun c hc => hx c (hIcontains i hi c hc)⟩
  let E : ℕ → Set (Literal V → ℝ) := fun i => {δ |
    decide (literalScore rep G (F i) δ (v,false) < literalScore rep G (F i) δ (v,true)) ≠
    decide (literalScore rep G (F (i+1)) δ (v,false) < literalScore rep G (F (i+1)) δ (v,true))}
  let Z : ℕ → Set (Literal V → ℝ) := fun i => {δ | ∃ a ∈ sets i, ∃ b ∈ sets (i+1),
    0 < δ a - d' a ∧ 0 < δ b - d' b ∧
    (∀ j ∈ sets i, j ≠ a → δ j - d' j < δ a - d' a) ∧
    (∀ j ∈ sets (i+1), δ j - d' j ≤ δ b - d' b) ∧ label a ≠ label b}
  have hpos : ∀ᵐ δ ∂μ, ∀ r, 0 < δ r := finite_independent_exponential_positive_ae β hβ
  have hdistinct : ∀ᵐ δ ∂μ, ∀ a b, a ≠ b → δ a - d' a ≠ δ b - d' b :=
    finite_shifted_exponential_scores_pairwise_distinct_ae β hβ d'
  have hbound (i : ℕ) (hi : i < k) : μ.real (E i) ≤ μ.real (Z i) := by
    apply ENNReal.toReal_mono (measure_ne_top μ _)
    apply measure_mono_ae
    filter_upwards [hpos,hdistinct] with δ hδ hdis hchange
    obtain ⟨a,haC,haF,haLabel,haPos,haMax⟩ := henc (F i) (hbase i (by omega)) (hsat i (by omega)) δ hδ
    obtain ⟨b,hbC,hbF,hbLabel,hbPos,hbMax⟩ := henc (F (i+1)) (hbase (i+1) (by omega)) (hsat (i+1) (by omega)) δ hδ
    have ha : a ∈ sets i := (hsets i a).mpr ⟨haC,haF⟩
    have hb : b ∈ sets (i+1) := (hsets (i+1) b).mpr ⟨hbC,hbF⟩
    have hda : d' a = d a := by simp [d',haC]
    have hdb : d' b = d b := by simp [d',hbC]
    refine ⟨a,ha,b,hb,?_,?_,?_,?_,?_⟩
    · simpa [hda] using haPos
    · simpa [hdb] using hbPos
    · intro j hj hja
      obtain ⟨hjC,hjF⟩ := (hsets i j).mp hj
      have hdj : d' j = d j := by simp [d',hjC]
      have hle : δ j - d' j ≤ δ a - d' a := by simpa [hdj,hda] using haMax j hjC hjF
      exact lt_of_le_of_ne hle (hdis j a hja)
    · intro j hj
      obtain ⟨hjC,hjF⟩ := (hsets (i+1) j).mp hj
      have hdj : d' j = d j := by simp [d',hjC]
      simpa [hdj,hdb] using hbMax j hjC hjF
    · rw [haLabel,hbLabel]
      exact hchange
  have hsum := shifted_exponential_nested_positive_changes_le_harmonic sets k hnested label d' hd' β hβ
  have hcard : (sets 0).card ≤ Fintype.card (Literal V) := Finset.card_le_univ _
  calc
    (∑ i ∈ Finset.range k, μ.real (E i)) ≤ ∑ i ∈ Finset.range k, μ.real (Z i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hbound i (Finset.mem_range.mp hi)
    _ ≤ (harmonic (sets 0).card : ℝ) := hsum
    _ ≤ (harmonic (Fintype.card (Literal V)) : ℝ) := harmonic_real_mono hcard
