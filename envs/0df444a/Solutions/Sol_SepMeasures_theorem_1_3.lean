-- Prove2me | solution 1 for SepMeasures.theorem_1_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T03:58:03.413681+00:00
-- url     : https://prove2.me/submissions/c1f1171c-61c5-40ec-9a79-90efca604aae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SepMeasures_CutValue
import Definitions.Def_SepMeasures_Families
import Theorems.Thm_SepMeasures_theorem_3_1
import Theorems.Thm_SepMeasures_theorem_3_2
import Theorems.Thm_SepMeasures_theorem_3_3

open MeasureTheory SepMeasures

namespace Aux13

lemma affGenPos_one (S : Set (E 1)) : AffGenPos 1 S := by
  intro t _ hcard
  by_cases hsub : Subsingleton (t : Set (E 1))
  · exact affineIndependent_of_subsingleton ℝ _
  · rw [subsingleton_iff] at hsub
    push Not at hsub
    obtain ⟨a, b, _⟩ := hsub
    rw [affineIndependent_iff_linearIndependent_vsub ℝ _ a]
    have huniq : Subsingleton {x : (t : Set (E 1)) // x ≠ a} := by
      refine ⟨fun x y => ?_⟩
      by_contra hxy
      have h1 : x.1.1 ≠ y.1.1 := fun h => hxy (Subtype.ext (Subtype.ext h))
      have h2 : x.1.1 ≠ a.1 := fun h => x.2 (Subtype.ext h)
      have h3 : y.1.1 ≠ a.1 := fun h => y.2 (Subtype.ext h)
      have hcard3 : 3 ≤ ({x.1.1, y.1.1, a.1} : Finset (E 1)).card := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [h3]
        · simp [h1, h2]
      have hle : ({x.1.1, y.1.1, a.1} : Finset (E 1)).card ≤ t.card := by
        apply Finset.card_le_card
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact x.1.2
        · exact y.1.2
        · exact a.2
      omega
    refine Fintype.linearIndependent_iff.mpr (fun g hg i => ?_)
    have hsum : (∑ j, g j • (j.1.1 -ᵥ a.1)) = g i • (i.1.1 -ᵥ a.1) := by
      rw [Finset.sum_eq_single i]
      · intro j _ hji; exact False.elim (hji (Subsingleton.elim j i))
      · intro hi; exact False.elim (hi (Finset.mem_univ i))
    rw [hsum] at hg
    have hne0 : (i.1.1 -ᵥ a.1) ≠ 0 := vsub_ne_zero.mpr (fun h => i.2 (Subtype.ext h))
    exact (smul_eq_zero.mp hg).resolve_right hne0

lemma atoms_dirac (z : E 1) : atoms (Measure.dirac z) = {z} := by
  ext w
  simp only [atoms, Set.mem_setOf, Set.mem_singleton_iff]
  rw [Measure.dirac_apply' _ (measurableSet_singleton w)]
  by_cases hw : w = z
  · subst hw; simp
  · simp [Set.indicator_of_notMem (Set.mem_singleton_iff.not.mpr (Ne.symm hw)), hw]

lemma dirac_pair_mem_P_one (N : Seminorm ℝ (E 1)) (hN : ∀ x, N x = 0 → x = 0) :
    ∃ p : Measure (E 1) × Measure (E 1), p ∈ P 1 N ∧ 0 < totalDist N p.1 p.2 := by
  let e₀ : E 1 := EuclideanSpace.single 0 1
  have he₀ : e₀ ≠ 0 := by
    intro h
    have : e₀ 0 = (0 : E 1) 0 := congrArg (fun v => v 0) h
    simp [e₀] at this
  refine ⟨(Measure.dirac 0, Measure.dirac e₀), ?_, ?_⟩
  · refine ⟨⟨inferInstance, inferInstance, ?_, ?_⟩, ?_, affGenPos_one _, ?_⟩
    · simp [FiniteFirstMoment, lintegral_dirac]
    · simp [FiniteFirstMoment, lintegral_dirac]
    · simp only [atoms_dirac, Set.disjoint_singleton]
      exact he₀.symm
    · intro H
      have hna : ∀ z : E 1, nonatomic (Measure.dirac z) H.set = 0 := by
        intro z
        have hms : MeasurableSet (H.set ∩ ({z} : Set (E 1))ᶜ) :=
          (isClosed_eq (continuous_const.inner continuous_id) continuous_const).measurableSet.inter
            (measurableSet_singleton z).compl
        rw [nonatomic, atoms_dirac, Measure.restrict_apply' (measurableSet_singleton z).compl,
          Measure.dirac_apply' _ hms]
        simp
      exact ⟨hna 0, hna e₀⟩
  · simp only [totalDist]
    rw [Measure.dirac_prod_dirac, integral_dirac]
    have hpos : 0 ≤ N ((0 : E 1) - e₀) := apply_nonneg N _
    refine lt_of_le_of_ne hpos (fun h => ?_)
    have hzero : (0 : E 1) - e₀ = 0 := hN _ h.symm
    exact he₀ (sub_eq_zero.mp hzero).symm

lemma cutRatio_Pf_le_P_one (N : Seminorm ℝ (E 1)) (hN : ∀ x, N x = 0 → x = 0) :
    cutRatio N (Pf 1 N) ≤ cutRatio N (P 1 N) := by
  unfold cutRatio
  obtain ⟨p₀, hp₀P, hp₀L⟩ := dirac_pair_mem_P_one N hN
  have : Nonempty {p : Measure (E 1) × Measure (E 1) // p ∈ P 1 N ∧ 0 < totalDist N p.1 p.2} :=
    ⟨⟨p₀, hp₀P, hp₀L⟩⟩
  have hbdd : BddBelow (Set.range fun q : {p : Measure (E 1) × Measure (E 1) //
      p ∈ Pf 1 N ∧ 0 < totalDist N p.1 p.2} =>
        ⨆ H : Hyp 1, cutVal N q.1.1 q.1.2 H / totalDist N q.1.1 q.1.2) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact Real.iSup_nonneg (fun H =>
      div_nonneg (integral_nonneg (fun _ => apply_nonneg N _)) q.2.2.le)
  refine le_ciInf (fun q => ?_)
  exact ciInf_le hbdd ⟨q.1, q.2.1.1, q.2.2⟩

end Aux13

theorem solution (d : ℕ) (hd : 1 ≤ d) (N : Seminorm ℝ (E d)) (hN : ∀ x, N x = 0 → x = 0) :
    (1 / 3 : ℝ) ≤ cutRatio N (P d N) := by
  by_cases hd3 : 3 ≤ d
  · exact SepMeasures.theorem_3_2 d hd3 N hN
  · interval_cases d
    · exact (SepMeasures.theorem_3_1 N hN).trans (Aux13.cutRatio_Pf_le_P_one N hN)
    · exact SepMeasures.theorem_3_3 N hN
