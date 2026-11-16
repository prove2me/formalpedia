-- Prove2me | solution 1 for Thm11SourceRoute.isCompact_goodRemainder
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T15:27:09.081648+00:00
-- url     : https://prove2.me/submissions/c25b49d9-71d1-478d-8866-cf58f5febb02

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F008
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F000
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep
open Finset BigOperators
open Set Topology
noncomputable section
open Thm11SourceRoute

theorem t11_pts_mem {a b : ℝ} (P : Partition a b) (j : Fin (P.n + 1)) : P.pts j ∈ Icc a b := by
  constructor
  · have h := P.strict_mono.monotone (Fin.zero_le j)
    rwa [P.pts_start] at h
  · have h := P.strict_mono.monotone (Fin.le_last j)
    rwa [P.pts_end] at h

theorem t11_sub_subset {a b : ℝ} (P : Partition a b) (i : Fin P.n) :
    Partition.subinterval P i ⊆ Icc a b := by
  intro x hx
  exact ⟨(t11_pts_mem P i.castSucc).1.trans hx.1, hx.2.trans (t11_pts_mem P i.succ).2⟩

theorem t11_left_mem {a b : ℝ} (P : Partition a b) (i : Fin P.n) :
    P.pts i.castSucc ∈ Partition.subinterval P i :=
  ⟨le_rfl, (P.strict_mono Fin.castSucc_lt_succ).le⟩

theorem t11_lower_le_upper {f : ℝ → ℝ} {a b : ℝ} (P : Partition a b) (i : Fin P.n)
    (hAbove : BddAbove (f '' Icc a b)) (hBelow : BddBelow (f '' Icc a b)) :
    lowerStep P f i ≤ upperStep P f i := by
  unfold lowerStep upperStep
  exact csInf_le_csSup ⟨_, Set.mem_image_of_mem f (t11_left_mem P i)⟩
    (hBelow.mono (Set.image_mono (t11_sub_subset P i)))
    (hAbove.mono (Set.image_mono (t11_sub_subset P i)))

theorem t11_incr_nonneg {f α : ℝ → ℝ} {a b : ℝ} (hs : SourceHypotheses a b f α)
    (P : Partition a b) (i : Fin P.n) :
    0 ≤ α (P.pts i.succ) - α (P.pts i.castSucc) :=
  sub_nonneg.2 (hs.2.2.2 (t11_pts_mem P _) (t11_pts_mem P _) (P.strict_mono Fin.castSucc_lt_succ).le)

theorem sol_mem_goodRemainder_iff {a b x : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ} :
    x ∈ goodRemainder a b S rho ↔
      x ∈ Icc a b ∧ ∀ c : ℝ, c ∈ S → rho c ≤ |x - c| := by
  unfold goodRemainder
  simp only [mem_inter_iff, mem_iInter, mem_setOf_eq]

theorem sol_isCompact_goodRemainder {a b : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ} :
    IsCompact (goodRemainder a b S rho) := by
  unfold goodRemainder
  refine isCompact_Icc.inter_right ?_
  refine isClosed_biInter fun c _ => ?_
  exact isClosed_le continuous_const (continuous_abs.comp (continuous_id.sub continuous_const))

theorem sol_upperSum_sub_lowerSum_eq_partitionOscillation {f α : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b) :
    upperSum P f α - lowerSum P f α =
      partitionOscillation P f α := by
  unfold upperSum lowerSum partitionOscillation
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem sol_partitionOscillation_nonneg_of_source {f α : ℝ → ℝ} {a b : ℝ}
    (hs : SourceHypotheses a b f α)
    (P : Partition a b) :
    0 ≤ partitionOscillation P f α := by
  unfold partitionOscillation
  refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ (t11_incr_nonneg hs P i)
  exact sub_nonneg.2 (t11_lower_le_upper P i hs.2.1 hs.2.2.1)

theorem sol_upperSum_sub_lowerSum_nonneg_of_source {f α : ℝ → ℝ} {a b : ℝ}
    (hs : SourceHypotheses a b f α)
    (P : Partition a b) :
    0 ≤ upperSum P f α - lowerSum P f α := by
  rw [sol_upperSum_sub_lowerSum_eq_partitionOscillation]
  exact sol_partitionOscillation_nonneg_of_source hs P

theorem sol_mem_badCellIndices_iff {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ) {i : ℕ} :
    i ∈ badCellIndices P S rho ↔
      i < P.n ∧
        ∀ hi : i < P.n,
          ¬ Partition.subinterval P ⟨i, hi⟩ ⊆ goodRemainder a b S rho := by
  unfold badCellIndices
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hi, h⟩
    refine ⟨hi, fun hi' => ?_⟩
    change ¬ (if h : i < P.n then Partition.subinterval P ⟨i, h⟩ else ∅) ⊆
      goodRemainder a b S rho at h
    rwa [dif_pos hi'] at h
  · rintro ⟨hi, h⟩
    refine ⟨hi, ?_⟩
    change ¬ (if h : i < P.n then Partition.subinterval P ⟨i, h⟩ else ∅) ⊆
      goodRemainder a b S rho
    rw [dif_pos hi]
    exact h hi

theorem sol_cell_subset_goodRemainder_of_not_mem_badCellIndices {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ)
    (i : Fin P.n)
    (hi_not_bad : i.val ∉ badCellIndices P S rho) :
    Partition.subinterval P i ⊆ goodRemainder a b S rho := by
  rw [sol_mem_badCellIndices_iff] at hi_not_bad
  push_neg at hi_not_bad
  obtain ⟨_, h⟩ := hi_not_bad i.2
  exact h

theorem sol_exists_bad_point_of_mem_badCellIndices {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ)
    {i : ℕ} (hi_bad : i ∈ badCellIndices P S rho) :
    ∃ c : ℝ, c ∈ S ∧ ∃ x : ℝ,
      ∃ hi : i < P.n, x ∈ Partition.subinterval P ⟨i, hi⟩ ∧ |x - c| < rho c := by
  rw [sol_mem_badCellIndices_iff] at hi_bad
  obtain ⟨hi, h⟩ := hi_bad
  have h2 := h hi
  rw [Set.not_subset] at h2
  obtain ⟨x, hx, hxg⟩ := h2
  rw [sol_mem_goodRemainder_iff] at hxg
  push_neg at hxg
  obtain ⟨c, hc, hlt⟩ := hxg (t11_sub_subset P _ hx)
  exact ⟨c, hc, x, hi, hx, hlt⟩

theorem sol_continuousOn_goodRemainder
    {f : ℝ → ℝ} {a b : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ}
    (hS : ∀ x : ℝ, x ∈ S ↔ x ∈ discontinuitySetOn f a b)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c) :
    ContinuousOn f (goodRemainder a b S rho) := by
  intro x hx
  rw [sol_mem_goodRemainder_iff] at hx
  have hxS : x ∉ S := by
    intro hxS
    have := hx.2 x hxS
    simp at this
    linarith [hrho_pos x hxS]
  have hcont : ContinuousWithinAt f (Icc a b) x := by
    by_contra hc
    exact hxS ((hS x).2 ⟨hx.1, hc⟩)
  exact hcont.mono (fun y hy => ((sol_mem_goodRemainder_iff).1 hy).1)

theorem sol_upperStep_sub_lowerStep_le_two_mul_abs_bound
    {f : ℝ → ℝ} {a b C : ℝ}
    (P : Partition a b) (i : Fin P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hC : ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C) :
    upperStep P f i - lowerStep P f i ≤ 2 * C := by
  have hne : (f '' Partition.subinterval P i).Nonempty := ⟨_, Set.mem_image_of_mem f (t11_left_mem P i)⟩
  have hU : upperStep P f i ≤ C := by
    unfold upperStep
    refine csSup_le hne ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (le_abs_self _).trans (hC x (t11_sub_subset P i hx))
  have hL : -C ≤ lowerStep P f i := by
    unfold lowerStep
    refine le_csInf hne ?_
    rintro _ ⟨x, hx, rfl⟩
    exact neg_le_of_abs_le (hC x (t11_sub_subset P i hx))
  linarith

theorem solution {a b : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ} :
    IsCompact (goodRemainder a b S rho) := by
  apply sol_isCompact_goodRemainder <;> assumption
