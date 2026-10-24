-- Prove2me | solution 1 for SecretaryAdvice.Memoryless.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T00:51:04.368163+00:00
-- url     : https://prove2.me/submissions/4b9e1a14-b06a-46ab-bdc9-99c509166317

import Mathlib
import Definitions.Def_SecretaryAdvice_Memoryless_Setting
import Definitions.Def_SecretaryAdvice_Memoryless_LP
import Theorems.Thm_SecretaryAdvice_Memoryless_proposition_9
import Theorems.Thm_SecretaryAdvice_Memoryless_proposition_10

open SecretaryAdvice.Memoryless

namespace SMA_T8

variable {n : ℕ} {S : Type} [Fintype S]

lemma prob_nonneg' (μ : SignalingStructure n S) (E : Outcome n S → Prop) : 0 ≤ prob μ E := by
  unfold prob
  refine Finset.sum_nonneg fun ω _ => ?_
  split_ifs
  · exact μ.nonneg ω
  · exact le_rfl

lemma c_nonneg (μ : SignalingStructure n S) (i : Fin n) (s : S) (j : Fin n) (s' : S) :
    0 ≤ c μ i s j s' :=
  div_nonneg (prob_nonneg' _ _) (prob_nonneg' _ _)

lemma feasible_bound (μ : SignalingStructure n S) (z : Fin n → S → ℝ) (hz : LPFeasible μ z)
    (i : Fin n) (s : S) : z i s ≤ 1 := by
  have h1 := hz.2 i s
  have h2 : 0 ≤ ∑ j ∈ Finset.Iio i, ∑ s', z j s' * c μ i s j s' :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun s' _ =>
      mul_nonneg (hz.1 j s') (c_nonneg μ i s j s')
  unfold slack at h1
  linarith

lemma exists_LP_max (μ : SignalingStructure n S) :
    ∃ z, LPFeasible μ z ∧ ∀ z', LPFeasible μ z' → LPObj μ z' ≤ LPObj μ z := by
  set K : Set (Fin n → S → ℝ) := {z | LPFeasible μ z} with hK
  have hclosed : IsClosed K := by
    have : K = (⋂ i, ⋂ s, {z : Fin n → S → ℝ | 0 ≤ z i s}) ∩
        (⋂ i, ⋂ s, {z : Fin n → S → ℝ | z i s ≤ slack μ z i s}) := by
      ext z
      simp [hK, LPFeasible]
    rw [this]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun s => ?_)
      (isClosed_iInter fun i => isClosed_iInter fun s => ?_)
    · exact isClosed_le continuous_const (by fun_prop)
    · refine isClosed_le (by fun_prop) ?_
      unfold slack
      fun_prop
  have hsub : K ⊆ Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : S => Set.Icc (0:ℝ) 1)) := by
    intro z hz i _ s _
    exact ⟨hz.1 i s, feasible_bound μ z hz i s⟩
  have hcpt : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset
      hclosed hsub
  have hne : K.Nonempty := by
    refine ⟨0, fun i s => le_rfl, fun i s => ?_⟩
    simp [slack]
  have hcont : ContinuousOn (LPObj μ) K := by
    apply Continuous.continuousOn
    unfold LPObj
    fun_prop
  obtain ⟨z, hzK, hmax⟩ := hcpt.exists_isMaxOn hne hcont
  exact ⟨z, hzK, fun z' hz' => hmax hz'⟩

end SMA_T8

theorem solution {n : ℕ} {S : Type} [Fintype S] (μ : SignalingStructure n S)
    (hNF : NonFiltering μ) (hHI : HistoryIrrelevance μ) :
    ∃ m : Policy n S, ValidPolicy m ∧ IsMemoryless m ∧
      ∀ q : Policy n S, ValidPolicy q → win μ q ≤ win μ m := by
  obtain ⟨z, hz, hmax⟩ := SMA_T8.exists_LP_max μ
  obtain ⟨m, hmv, hmm, hmw⟩ := proposition_10 μ hNF hHI z hz
  refine ⟨m, hmv, hmm, fun q hq => ?_⟩
  obtain ⟨zq, hzq, hzw⟩ := proposition_9 μ hNF hHI q hq
  rw [← hzw, hmw]
  exact hmax zq hzq
