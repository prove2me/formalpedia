-- Prove2me | solution 1 for OceanicGames.Limit.equation_3_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T22:08:08.508065+00:00
-- url     : https://prove2.me/submissions/5699f753-de7d-46e5-84e7-ce90c347cf94

import Mathlib
import Definitions.Def_OceanicGames_Limit_Basic



namespace OceanicGames.Limit

open MeasureTheory Set Finset

theorem orderSet_meas {m : ℕ} (i : Fin m) (S : Finset (Fin m)) :
    MeasurableSet (orderSet i S) := by
  unfold orderSet
  have h1 : MeasurableSet (OceanicGames.Interior.cube m) := measurableSet_Icc
  have h2 : MeasurableSet {x : Fin m → ℝ | ∀ j ∈ S, x j < x i} := by
    have : {x : Fin m → ℝ | ∀ j ∈ S, x j < x i} = ⋂ j ∈ S, {x | x j < x i} := by
      ext x; simp
    rw [this]
    exact Finset.measurableSet_biInter S fun j _ =>
      measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)
  have h3 : MeasurableSet {x : Fin m → ℝ | ∀ j ∉ S, x i ≤ x j} := by
    have : {x : Fin m → ℝ | ∀ j ∉ S, x i ≤ x j} = ⋂ j ∈ Sᶜ, {x | x i ≤ x j} := by
      ext x; simp
    rw [this]
    exact Finset.measurableSet_biInter Sᶜ fun j _ =>
      measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)
  exact h1.inter (h2.inter h3)

theorem pred_eq_of_mem_orderSet {m : ℕ} {i : Fin m} {S : Finset (Fin m)} {x : Fin m → ℝ}
    (hx : x ∈ orderSet i S) : OceanicGames.Interior.pred x (x i) = S := by
  obtain ⟨_, h1, h2⟩ := hx
  ext j
  simp only [OceanicGames.Interior.pred, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra hj
    exact absurd (h2 j hj) (not_le.2 h)
  · intro hj; exact h1 j hj

theorem pivot_inter_order {m : ℕ} (c alpha : ℝ) (w : Fin m → ℝ) (i : Fin m)
    (S : Finset (Fin m)) :
    OceanicGames.Interior.pivotSet c alpha w i ∩ orderSet i S =
      orderSet i S ∩ {x | OceanicGames.Interior.wsum w S + alpha * x i ≤ c ∧
        c ≤ OceanicGames.Interior.wsum w S + w i + alpha * x i} := by
  ext x
  constructor
  · rintro ⟨⟨_, h1, h2⟩, hx⟩
    rw [pred_eq_of_mem_orderSet hx] at h1 h2
    exact ⟨hx, h1, h2⟩
  · rintro ⟨hx, h1, h2⟩
    refine ⟨⟨hx.1, ?_, ?_⟩, hx⟩
    · rw [pred_eq_of_mem_orderSet hx]; exact h1
    · rw [pred_eq_of_mem_orderSet hx]; exact h2

theorem equation_3_4_core {m : ℕ} (c alpha : ℝ) (w : Fin m → ℝ) (i : Fin m) :
    OceanicGames.Interior.value c alpha w i =
      ∑ S ∈ (Finset.univ.erase i).powerset,
        (volume (OceanicGames.Interior.pivotSet c alpha w i ∩ orderSet i S)).toReal := by
  classical
  unfold OceanicGames.Interior.value
  have hmeas : ∀ S : Finset (Fin m), MeasurableSet
      (OceanicGames.Interior.pivotSet c alpha w i ∩ orderSet i S) := by
    intro S
    rw [pivot_inter_order]
    refine (orderSet_meas i S).inter ?_
    have hf : Measurable fun x : Fin m → ℝ => OceanicGames.Interior.wsum w S + alpha * x i := by
      fun_prop
    have hg : Measurable fun x : Fin m → ℝ => OceanicGames.Interior.wsum w S + w i + alpha * x i := by
      fun_prop
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_le hf measurable_const
    · exact measurableSet_le measurable_const hg
  have hU : OceanicGames.Interior.pivotSet c alpha w i =
      ⋃ S ∈ (Finset.univ.erase i).powerset,
        (OceanicGames.Interior.pivotSet c alpha w i ∩ orderSet i S) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
    constructor
    · intro hx
      refine ⟨OceanicGames.Interior.pred x (x i), ?_, hx, ?_⟩
      · rw [Finset.mem_powerset]
        intro j hj
        simp only [OceanicGames.Interior.pred, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        rintro rfl
        exact lt_irrefl _ hj
      · refine ⟨hx.1, ?_, ?_⟩
        · intro j hj
          simpa [OceanicGames.Interior.pred] using hj
        · intro j hj
          simpa [OceanicGames.Interior.pred] using hj
    · rintro ⟨S, _, hx, _⟩; exact hx
  have hfin : ∀ S : Finset (Fin m),
      volume (OceanicGames.Interior.pivotSet c alpha w i ∩ orderSet i S) ≠ ⊤ := by
    intro S
    have hc : volume (Set.Icc (0 : Fin m → ℝ) 1) < ⊤ := isCompact_Icc.measure_lt_top
    refine ne_top_of_le_ne_top hc.ne ?_
    apply measure_mono
    exact fun x hx => hx.1.1
  conv_lhs => rw [hU]
  rw [measure_biUnion_finset, ENNReal.toReal_sum]
  · intro S _; exact hfin S
  · intro S _ S' _ hne
    refine Set.disjoint_left.2 ?_
    intro x hx hx'
    exact hne ((pred_eq_of_mem_orderSet hx.2).symm.trans (pred_eq_of_mem_orderSet hx'.2))
  · intro S _; exact hmeas S

end OceanicGames.Limit

open OceanicGames.Limit
open MeasureTheory Set Finset

theorem solution {m : ℕ} (c alpha : ℝ) (w : Fin m → ℝ) (i : Fin m)
    (hc : 0 ≤ c) (halpha : 0 < alpha) (hw : ∀ j, 0 ≤ w j) :
    OceanicGames.Interior.value c alpha w i =
      ∑ S ∈ (Finset.univ.erase i).powerset,
        (volume (OceanicGames.Interior.pivotSet c alpha w i ∩ orderSet i S)).toReal := by
  exact equation_3_4_core c alpha w i
