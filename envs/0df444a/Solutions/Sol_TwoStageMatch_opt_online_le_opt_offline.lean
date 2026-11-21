-- Prove2me | solution 1 for TwoStageMatch.opt_online_le_opt_offline
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:52:43.776117+00:00
-- url     : https://prove2.me/submissions/cc41b6f5-d7eb-456b-b4a1-f2a42f033bcd

import Mathlib
import Definitions.Def_TwoStageMatch_Instance

namespace Aux_TwoStageMatch_opt_online_le_opt_offline

open TwoStageMatch

theorem mem_matchings {U S : Type*} [Fintype U] [Fintype S] (E : U → S → Prop) (X : Finset U)
    (Y : Finset S) (M : Finset (U × S)) :
    M ∈ matchings E X Y ↔ IsMatching E X Y M := by
  simp [matchings]

theorem part1 {D₁ D₂ S : Type*} [Fintype D₁] [Fintype D₂] [Fintype S]
    [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S] (I : Instance D₁ D₂ S) :
    ∀ M, IsFirstStageMatching I M → ∀ A : Finset D₂,
      twoStageWeight I M A ≤ maxWeightMatch I.E I.w (firstStage ∪ secondStage A) Finset.univ := by
  intro M hM A
  have hM' : IsMatching I.E firstStage Finset.univ M := hM
  unfold twoStageWeight maxWeightMatch
  obtain ⟨N, hN, hNeq⟩ := Finset.exists_mem_eq_sup'
    (matchings_nonempty I.E (secondStage A) (Finset.univ \ matchedSupply M)) (weight I.w)
  rw [hNeq]
  have hNm : IsMatching I.E (secondStage A) (Finset.univ \ matchedSupply M) N :=
    (mem_matchings _ _ _ _).mp hN
  -- supplies used by N are not used by M
  have hsupp : ∀ e ∈ N, e.2 ∉ matchedSupply M := by
    intro e he
    have := (hNm.1 e he).2.2
    rw [Finset.mem_sdiff] at this
    exact this.2
  have hdisj : Disjoint (matchedSupply M) (matchedSupply N) := by
    rw [Finset.disjoint_left]
    intro a haM haN
    unfold matchedSupply at haN
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp haN
    exact hsupp e he haM
  have hfirst : ∀ e ∈ M, ∃ a : D₁, e.1 = Sum.inl a := by
    intro e he
    have h := (hM'.1 e he).2.1
    unfold firstStage at h
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
    exact ⟨a, ha.symm⟩
  have hsecond : ∀ e ∈ N, ∃ b : D₂, e.1 = Sum.inr b := by
    intro e he
    have h := (hNm.1 e he).2.1
    unfold secondStage at h
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp h
    exact ⟨b, hb.symm⟩
  have hMsupp : ∀ e ∈ M, e.2 ∈ matchedSupply M := by
    intro e he
    unfold matchedSupply
    exact Finset.mem_image_of_mem _ he
  have hU : IsMatching I.E (firstStage ∪ secondStage A) Finset.univ (M ∪ N) := by
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      rcases Finset.mem_union.mp he with he | he
      · obtain ⟨h1, h2, h3⟩ := hM'.1 e he
        exact ⟨h1, Finset.mem_union_left _ h2, Finset.mem_univ _⟩
      · obtain ⟨h1, h2, _⟩ := hNm.1 e he
        exact ⟨h1, Finset.mem_union_right _ h2, Finset.mem_univ _⟩
    · intro e he e' he' h
      rcases Finset.mem_union.mp he with he | he <;>
        rcases Finset.mem_union.mp he' with he' | he'
      · exact hM'.2.1 e he e' he' h
      · obtain ⟨a, ha⟩ := hfirst e he
        obtain ⟨b, hb⟩ := hsecond e' he'
        rw [ha, hb] at h
        exact absurd h Sum.inl_ne_inr
      · obtain ⟨b, hb⟩ := hsecond e he
        obtain ⟨a, ha⟩ := hfirst e' he'
        rw [ha, hb] at h
        exact absurd h Sum.inr_ne_inl
      · exact hNm.2.1 e he e' he' h
    · intro e he e' he' h
      rcases Finset.mem_union.mp he with he | he <;>
        rcases Finset.mem_union.mp he' with he' | he'
      · exact hM'.2.2 e he e' he' h
      · exact absurd (show e'.2 ∈ matchedSupply M from h ▸ hMsupp e he) (hsupp e' he')
      · exact absurd (show e.2 ∈ matchedSupply M from h ▸ hMsupp e' he') (hsupp e he)
      · exact hNm.2.2 e he e' he' h
  have hw : weight I.w (M ∪ N) = weight I.w M + weight I.w N := by
    unfold weight
    have : matchedSupply (M ∪ N) = matchedSupply M ∪ matchedSupply N := by
      unfold matchedSupply
      exact Finset.image_union M N
    rw [this, Finset.sum_union hdisj]
  rw [← hw]
  exact Finset.le_sup' (weight I.w) ((mem_matchings _ _ _ _).mpr hU)

end Aux_TwoStageMatch_opt_online_le_opt_offline

open TwoStageMatch Aux_TwoStageMatch_opt_online_le_opt_offline in
theorem solution {D₁ D₂ S : Type*} [Fintype D₁] [Fintype D₂] [Fintype S]
    [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S] (I : Instance D₁ D₂ S) :
    (∀ M, IsFirstStageMatching I M → ∀ A : Finset D₂,
      twoStageWeight I M A ≤ maxWeightMatch I.E I.w (firstStage ∪ secondStage A) Finset.univ) ∧
    optOnline I ≤ optOffline I := by
  refine ⟨part1 I, ?_⟩
  have hp : ∀ A : Finset D₂, 0 ≤ arrivalProb I A := by
    intro A
    unfold arrivalProb
    exact mul_nonneg (Finset.prod_nonneg (fun i _ => I.π_nonneg i))
      (Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (I.π_le_one i)))
  have hsum1 : ∑ A : Finset D₂, arrivalProb I A = 1 := by
    have h := Finset.prod_add (fun i => I.π i) (fun i => 1 - I.π i) (Finset.univ : Finset D₂)
    simp only [add_sub_cancel, Finset.prod_const_one, Finset.powerset_univ] at h
    rw [h]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    unfold arrivalProb
    rw [Finset.compl_eq_univ_sdiff]
  unfold optOnline optOffline expect
  apply Finset.sup'_le
  intro M hM
  have hMm : IsFirstStageMatching I M := (mem_matchings _ _ _ _).mp hM
  have key : ∑ A : Finset D₂, arrivalProb I A *
        (weight I.w M + maxWeightMatch I.E I.w (secondStage A) (Finset.univ \ matchedSupply M))
      = weight I.w M + ∑ A : Finset D₂, arrivalProb I A *
          maxWeightMatch I.E I.w (secondStage A) (Finset.univ \ matchedSupply M) := by
    rw [Finset.sum_congr rfl (fun A _ => mul_add _ _ _), Finset.sum_add_distrib,
      ← Finset.sum_mul, hsum1, one_mul]
  rw [← key]
  refine Finset.sum_le_sum (fun A _ => mul_le_mul_of_nonneg_left ?_ (hp A))
  exact part1 I M hMm A
