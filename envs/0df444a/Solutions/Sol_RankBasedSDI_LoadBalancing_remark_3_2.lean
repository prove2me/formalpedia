-- Prove2me | solution 1 for RankBasedSDI.LoadBalancing.remark_3_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:51:53.463648+00:00
-- url     : https://prove2.me/submissions/6ed2a3a9-bc26-4ceb-9ccf-15a0d6488a01

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_Rank
import Definitions.Def_RankBasedSDI_LoadBalancing_StochasticBasis
import Definitions.Def_RankBasedSDI_LoadBalancing_Reflection
import Definitions.Def_RankBasedSDI_LoadBalancing_RankBasedEquations
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open BellWilliams2001.ThresholdPolicy

namespace Aux_RankBasedSDI_remark_3_2
open RankBasedSDI.LoadBalancing

theorem rc_union {N : ℕ} (x : Fin N → ℝ) (k : Fin N) :
    rankCount x k = ((Finset.univ.filter (fun l => x l < x k)) ∪
      (Finset.univ.filter (fun l => l ≤ k ∧ x l = x k))).card := by
  unfold rankCount
  rw [Finset.card_union_of_disjoint]
  rw [Finset.disjoint_filter]
  intro l _ h1 h2
  exact absurd h2.2 (ne_of_lt h1)

theorem rc_lt {N : ℕ} (x : Fin N → ℝ) (i j : Fin N)
    (h : x i < x j ∨ (x i = x j ∧ i < j)) : rankCount x i < rankCount x j := by
  rw [rc_union, rc_union]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨j, ?_, ?_⟩
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, rfl⟩)
    · intro hj
      rcases Finset.mem_union.mp hj with hj | hj
      · have := (Finset.mem_filter.mp hj).2
        rcases h with h | h
        · linarith
        · linarith [h.1]
      · obtain ⟨hji, hxe⟩ := (Finset.mem_filter.mp hj).2
        rcases h with h | h
        · linarith
        · exact absurd h.2 (not_lt.mpr hji)
  · intro l hl
    rcases Finset.mem_union.mp hl with hl | hl
    · have := (Finset.mem_filter.mp hl).2
      refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      rcases h with h | h
      · linarith
      · linarith [h.1]
    · obtain ⟨hli, hxe⟩ := (Finset.mem_filter.mp hl).2
      rcases h with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_trans hli h.2.le, by rw [hxe, h.1]⟩)

theorem rank_val {N : ℕ} (x : Fin N → ℝ) (i : Fin N) : (rank x i).val = rankCount x i - 1 := rfl

theorem rank_lt {N : ℕ} (x : Fin N → ℝ) (i j : Fin N)
    (h : x i < x j ∨ (x i = x j ∧ i < j)) : rank x i < rank x j := by
  rw [Fin.lt_iff_val_lt_val, rank_val, rank_val]
  have h1 := rc_lt x i j h
  have h2 := (rankCount_mem x i).1
  omega

theorem rank_inj {N : ℕ} (x : Fin N → ℝ) : Function.Injective (rank x) := by
  intro i j hij
  by_contra hne
  rcases lt_trichotomy (x i) (x j) with h | h | h
  · exact absurd hij (ne_of_lt (rank_lt x i j (Or.inl h)))
  · rcases lt_or_gt_of_ne hne with h' | h'
    · exact absurd hij (ne_of_lt (rank_lt x i j (Or.inr ⟨h, h'⟩)))
    · exact absurd hij.symm (ne_of_lt (rank_lt x j i (Or.inr ⟨h.symm, h'⟩)))
  · exact absurd hij.symm (ne_of_lt (rank_lt x j i (Or.inl h)))

theorem drift_mem {N : ℕ} (b : Fin N → ℝ) (x : Fin N → ℝ) : rankDrift b x ∈ driftSet b x := by
  have hinj := rank_inj x
  set π : Equiv.Perm (Fin N) :=
    Equiv.ofBijective (rank x) ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩ with hπ
  have hπmem : π ∈ permSet x := by
    intro i j h
    show rank x i < rank x j
    exact rank_lt x i j (Or.inl h)
  apply subset_convexHull
  exact ⟨π, hπmem, rfl⟩

theorem meas_rankCount {N : ℕ} (i : Fin N) : Measurable (fun x : Fin N → ℝ => rankCount x i) := by
  classical
  unfold rankCount
  simp only [Finset.card_filter]
  refine (Finset.measurable_sum _ fun j _ => ?_).add (Finset.measurable_sum _ fun j _ => ?_)
  · exact Measurable.ite (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i))
      measurable_const measurable_const
  · refine Measurable.ite ?_ measurable_const measurable_const
    by_cases hji : j ≤ i
    · simp only [hji, true_and]
      exact measurableSet_eq_fun (measurable_pi_apply j) (measurable_pi_apply i)
    · simp only [hji, false_and, Set.setOf_false, MeasurableSet.empty]

theorem meas_rankDrift {N : ℕ} (b : Fin N → ℝ) : Measurable (rankDrift (N := N) b) := by
  refine measurable_pi_lambda _ fun i => ?_
  have hr : Measurable (fun x : Fin N → ℝ => rank x i) := by
    refine measurable_to_countable' fun k => ?_
    have : (fun x : Fin N → ℝ => rank x i) ⁻¹' {k} =
        (fun x : Fin N → ℝ => rankCount x i - 1) ⁻¹' {k.val} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Fin.ext_iff, rank_val]
    rw [this]
    exact ((meas_rankCount i).sub_const 1) (measurableSet_singleton _)
  exact (measurable_of_countable b).comp hr

theorem progressive {N : ℕ} (b : Fin N → ℝ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) (X : Ω → ℝ → Fin N → ℝ)
    (hadapt : ∀ t : ℝ≥0, Measurable[F t] (fun ω => X ω t))
    (hcont : ∀ ω (i : Fin N), ContinuousOn (fun t => X ω t i) (Set.Ici 0)) :
    IsProgressive F (fun (t : ℝ≥0) ω => rankDrift b (X ω t)) := by
  have hSA : StronglyAdapted F (fun (t : ℝ≥0) ω => X ω t) := fun t =>
    (hadapt t).stronglyMeasurable
  have hc : ∀ ω, Continuous fun t : ℝ≥0 => X ω t := by
    intro ω
    refine continuous_pi fun i => ?_
    exact (hcont ω i).comp_continuous NNReal.continuous_coe fun t => t.2
  have hSP := hSA.isStronglyProgressive_of_continuous hc
  intro t
  exact (meas_rankDrift b).comp (hSP t).measurable

end Aux_RankBasedSDI_remark_3_2

open RankBasedSDI.LoadBalancing Aux_RankBasedSDI_remark_3_2 in
theorem solution {N : ℕ} (b m σ : Fin N → ℝ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (X L B : Ω → ℝ → Fin N → ℝ) :
    (IsWeakSolutionSDE b m σ P F X B →
      IsWeakSolutionSDI b m σ P F X B (fun ω t => rankDrift b (X ω t))) ∧
    (IsWeakSolutionSDER b m σ P F X L B →
      IsWeakSolutionSDIR b m σ P F X L B (fun ω t => rankDrift b (X ω t))) := by
  constructor
  · intro h
    exact
      { isProbability := h.isProbability
        usual := h.usual
        brownian := h.brownian
        adapted_X := h.adapted_X
        progressive_β := progressive b F X h.adapted_X h.continuous_X
        continuous_X := h.continuous_X
        equation := h.equation
        inclusion := Eventually.of_forall fun ω =>
          Eventually.of_forall fun t => drift_mem b (X ω t) }
  · intro h
    exact
      { isProbability := h.isProbability
        usual := h.usual
        brownian := h.brownian
        adapted_X := h.adapted_X
        adapted_L := h.adapted_L
        progressive_β := progressive b F X h.adapted_X h.continuous_X
        continuous_X := h.continuous_X
        nonneg_X := h.nonneg_X
        regulator_L := h.regulator_L
        equation := h.equation
        inclusion := Eventually.of_forall fun ω =>
          Eventually.of_forall fun t => drift_mem b (X ω t)
        complementary := h.complementary }
