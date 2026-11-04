-- Prove2me | solution 1 for StochKolmogorov.Classify.case_M2_empty
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T13:30:09.248774+00:00
-- url     : https://prove2.me/submissions/826c16c7-ca48-4ee5-b521-f8c1c9726a6d

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Classification
import Theorems.Thm_StochKolmogorov_Classify_delta_star_mem

set_option autoImplicit false
set_option linter.all false

section CM2Sec

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.CM2

open StochKolmogorov.Classify EthierKurtz

theorem supp_dirac {n : ℕ} : supp (Measure.dirac (0 : SDEState n)) = ∅ := by
  classical
  unfold supp
  rw [Finset.filter_eq_empty_iff]
  intro i _
  rw [not_not, Measure.dirac_apply, Set.indicator_of_notMem]
  simp

theorem eq_dirac_of_supp {n : ℕ} (μ : Measure (SDEState n)) [IsProbabilityMeasure μ]
    (horth : μ (orthant n)ᶜ = 0) (hs : supp μ = ∅) : μ = Measure.dirac (0 : SDEState n) := by
  classical
  have hi : ∀ i, μ {x : SDEState n | 0 < x i} = 0 := by
    intro i
    have h := Finset.filter_eq_empty_iff.1 hs (Finset.mem_univ i)
    exact not_not.1 h
  have hnull : μ ({(0 : SDEState n)}ᶜ) = 0 := by
    refine measure_mono_null (t := (orthant n)ᶜ ∪ ⋃ i, {x : SDEState n | 0 < x i}) ?_
      (measure_union_null horth (measure_iUnion_null hi))
    intro y hy
    by_contra hc
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, not_or,
      not_not, not_exists, not_lt] at hc
    apply hy
    show y = 0
    ext i
    have h1 : 0 ≤ y i := hc.1 i
    have h2 := hc.2 i
    simp only [PiLp.zero_apply]
    linarith
  ext s hs
  by_cases h0 : (0 : SDEState n) ∈ s
  · rw [Measure.dirac_apply_of_mem h0]
    have hsc : sᶜ ⊆ ({(0 : SDEState n)}ᶜ) := by
      intro y hy hy0
      rw [Set.mem_singleton_iff.1 hy0] at hy
      exact hy h0
    have hc : μ sᶜ = 0 := measure_mono_null hsc hnull
    exact (prob_compl_eq_zero_iff hs).1 hc
  · rw [Measure.dirac_apply' _ hs, Set.indicator_of_notMem h0]
    have hss : s ⊆ ({(0 : SDEState n)}ᶜ) := by
      intro y hy hy0
      rw [Set.mem_singleton_iff.1 hy0] at hy
      exact h0 hy
    exact measure_mono_null hss hnull

theorem main {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hδ : Measure.dirac (0 : SDEState n) ∈ bdryErgodic P X) (hM2 : M2 P C X = ∅) :
    M1 P C X = {Measure.dirac (0 : SDEState n)} ∧
      bdryErgodic P X = {Measure.dirac (0 : SDEState n)} := by
  have hsub : bdryErgodic P X ⊆ M1 P C X := by
    intro μ hμ
    by_contra h
    have hm : μ ∈ M2 P C X := ⟨hμ, h⟩
    rw [hM2] at hm
    exact hm
  have hδ1 : Measure.dirac (0 : SDEState n) ∈ M1 P C X := hsub hδ
  have hneg : ∀ i, lyap C i (Measure.dirac (0 : SDEState n)) < 0 := fun i =>
    hδ1.2.1 i (by rw [supp_dirac]; exact Finset.notMem_empty i)
  have honly : ∀ μ ∈ bdryErgodic P X, μ = Measure.dirac (0 : SDEState n) := by
    intro μ hμ
    have hs : supp μ = ∅ := by
      by_contra hne
      obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hne
      have hbd : (0 : SDEState n) ∈ faceBdry μ := by
        refine ⟨⟨fun i => le_refl _, fun i _ => rfl⟩, fun h => ?_⟩
        exact lt_irrefl _ (h.2 j hj)
      have hδsub : Measure.dirac (0 : SDEState n) ∈ subErgodic P X μ := by
        refine ⟨hδ, ?_⟩
        rw [Measure.dirac_apply, Set.indicator_of_notMem]
        exact fun h => h hbd
      obtain ⟨i, -, hi⟩ := (hsub hμ).2.2 ⟨j, hj⟩ (Measure.dirac (0 : SDEState n))
        ⟨{Measure.dirac (0 : SDEState n)}, fun _ => 1, by simpa using hδsub,
          fun _ _ => one_pos, by simp, by simp⟩
      exact lt_asymm hi (hneg i)
    haveI : IsProbabilityMeasure μ := hμ.1.1.1
    exact eq_dirac_of_supp μ hμ.1.1.2.1 hs
  exact ⟨Set.eq_singleton_iff_unique_mem.2 ⟨hδ1, fun μ hμ => honly μ hμ.1⟩,
    Set.eq_singleton_iff_unique_mem.2 ⟨hδ, honly⟩⟩

end StochKolmogorov.Classify.CM2

end CM2Sec

open MeasureTheory ProbabilityTheory Filter StochKolmogorov.Classify EthierKurtz in
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₁ : ℝ) (h14 : Assumption14 C δ₁)
    (hM2 : M2 P C X = ∅) (hM1 : (M1 P C X).Nonempty) :
    M1 P C X = {Measure.dirac (0 : SDEState n)} ∧
      bdryErgodic P X = {Measure.dirac (0 : SDEState n)} := by
  exact StochKolmogorov.Classify.CM2.main P C X (delta_star_mem hn P C B X hX c γb hA) hM2
