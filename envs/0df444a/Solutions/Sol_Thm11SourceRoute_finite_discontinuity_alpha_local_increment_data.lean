-- Prove2me | solution 1 for Thm11SourceRoute.finite_discontinuity_alpha_local_increment_data
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T15:37:27.738929+00:00
-- url     : https://prove2.me/submissions/c937a6c3-2787-44f8-83f6-4f1f89764c9a

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F001
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F005
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F006
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F008
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F001
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_darboux_gap_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_limit_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_limit_F001
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_finite_discontinuity_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_refinement_points_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_refinement_monotonicity_F000
import Mathlib.Data.List.GetD
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

theorem sol_closedIntervalDarbouxCommonLimitFromOscillation_of_gap
    (hdarboux : ClosedIntervalDarbouxCommonLimitFromGap) :
    ClosedIntervalDarbouxCommonLimitFromOscillation := by
  intro f α a b hs hosc
  apply hdarboux hs
  intro eps he
  obtain ⟨δ, hδ, h⟩ := hosc eps he
  exact ⟨δ, hδ, fun P hP => by rw [sol_upperSum_sub_lowerSum_eq_partitionOscillation]; exact h P hP⟩

theorem sol_strict_upperLower_criterion_of_oscillation
    (hdarboux : ClosedIntervalDarbouxCommonLimitFromOscillation)
    (hosc : StrictFiniteDiscontinuityOscillationCriterion) :
    StrictFiniteDiscontinuityUpperLowerCriterion := by
  intro f α a b hab hm hA hB hD hC
  exact hdarboux ⟨hab, hA, hB, hm.monotoneOn _⟩ (hosc hab hm hA hB hD hC)

theorem sol_strict_upperLower_criterion_of_gap
    (hdarboux : ClosedIntervalDarbouxCommonLimitFromGap)
    (hosc : StrictFiniteDiscontinuityOscillationCriterion) :
    StrictFiniteDiscontinuityUpperLowerCriterion :=
  sol_strict_upperLower_criterion_of_oscillation
    (sol_closedIntervalDarbouxCommonLimitFromOscillation_of_gap hdarboux) hosc

theorem sol_strict_thm_1_1_of_common_limit_criterion
    (hcriterion : StrictFiniteDiscontinuityCommonLimitCriterion)
    {f α : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hα_mono : Monotone α)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hDiscFinite : (discontinuitySetOn f a b).Finite)
    (hαCont : ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) :
    RSIntegrable f α a b := by
  obtain ⟨L, h1, h2⟩ := hcriterion hab hα_mono hAbove hBelow hDiscFinite hαCont
  exact ⟨⟨L, h1, h2⟩⟩

theorem sol_closedIntervalDarbouxAbsGapSmall_of_gapSmall
    {f α : ℝ → ℝ} {a b : ℝ}
    (hs : SourceHypotheses a b f α)
    (hgap : ClosedIntervalDarbouxGapSmall a b f α) :
    ∀ eps > 0, ∃ δ > 0, ∀ P : Partition a b,
      P.mesh < δ →
        |upperSum P f α - lowerSum P f α| < eps := by
  intro eps he
  obtain ⟨δ, hδ, h⟩ := hgap eps he
  refine ⟨δ, hδ, fun P hP => ?_⟩
  rw [abs_of_nonneg (sol_upperSum_sub_lowerSum_nonneg_of_source hs P)]
  exact h P hP

theorem sol_closedIntervalDarbouxFineCauchy_of_commonRefinementSandwich
    {f α : ℝ → ℝ} {a b : ℝ}
    (hs : SourceHypotheses a b f α)
    (hgap : ClosedIntervalDarbouxGapSmall a b f α)
    (hrefine : DarbouxCommonRefinementSandwich a b f α) :
    ClosedIntervalDarbouxFineCauchy a b f α := by
  intro eps he
  obtain ⟨δ, hδ, h⟩ := hgap (eps / 2) (by linarith)
  refine ⟨δ, hδ, fun P Q hP hQ => ?_⟩
  obtain ⟨R, hR, h1, h2, h3, h4⟩ := hrefine δ hδ P Q hP hQ
  have gP := h P hP
  have gQ := h Q hQ
  have nR := sol_upperSum_sub_lowerSum_nonneg_of_source hs R
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [abs_sub_lt_iff] <;> constructor <;> linarith

theorem sol_closedIntervalDarbouxFineCauchyFromGap_of_commonRefinementSandwich
    (hrefine :
      ∀ {f α : ℝ → ℝ} {a b : ℝ},
        SourceHypotheses a b f α →
        DarbouxCommonRefinementSandwich a b f α) :
    ClosedIntervalDarbouxFineCauchyFromGap := by
  intro f α a b hs hgap
  exact sol_closedIntervalDarbouxFineCauchy_of_commonRefinementSandwich hs hgap (hrefine hs)

theorem sol_DarbouxCommonRefinementSandwich_of_exists_and_sumMonotone
    {f α : ℝ → ℝ} {a b : ℝ}
    (hexists : DarbouxCommonRefinementExists a b)
    (hmono : DarbouxRefinementSumMonotone a b f α)
    (hs : SourceHypotheses a b f α) :
    DarbouxCommonRefinementSandwich a b f α := by
  intro δ hδ P Q hP hQ
  obtain ⟨R, hR, hRP, hRQ⟩ := hexists δ hδ P Q hP hQ
  obtain ⟨p1, p2⟩ := hmono hs P R hRP
  obtain ⟨q1, q2⟩ := hmono hs Q R hRQ
  exact ⟨R, hR, p1, q1, p2, q2⟩

theorem sol_exists_bad_point_of_not_subset_goodRemainder_cell
    {a b : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ}
    (P : Partition a b) {i : Fin P.n}
    (hcell_not_good :
      ¬ Partition.subinterval P i ⊆ goodRemainder a b S rho) :
    ∃ c : ℝ, c ∈ S ∧ ∃ x : ℝ,
      x ∈ Partition.subinterval P i ∧ |x - c| < rho c := by
  rw [Set.not_subset] at hcell_not_good
  obtain ⟨x, hx, hxg⟩ := hcell_not_good
  rw [sol_mem_goodRemainder_iff] at hxg
  push_neg at hxg
  obtain ⟨c, hc, hlt⟩ := hxg (t11_sub_subset P _ hx)
  exact ⟨c, hc, x, hx, hlt⟩

theorem sol_exists_bad_point_half_radius_of_not_subset_goodRemainder_cell
    {a b : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ}
    (P : Partition a b) {i : Fin P.n}
    (hcell_not_good :
      ¬ Partition.subinterval P i ⊆
        goodRemainder a b S (fun c : ℝ => rho c / 2)) :
    ∃ c : ℝ, c ∈ S ∧ ∃ x : ℝ,
      x ∈ Partition.subinterval P i ∧ |x - c| < rho c / 2 :=
  sol_exists_bad_point_of_not_subset_goodRemainder_cell P hcell_not_good

theorem sol_upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound
    {f : ℝ → ℝ} {a b eta : ℝ}
    (P : Partition a b) (i : Fin P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hosc :
      ∀ x, x ∈ Partition.subinterval P i →
      ∀ y, y ∈ Partition.subinterval P i → |f x - f y| ≤ eta) :
    upperStep P f i - lowerStep P f i ≤ eta := by
  have hne : (f '' Partition.subinterval P i).Nonempty := ⟨_, Set.mem_image_of_mem f (t11_left_mem P i)⟩
  have hBl : BddBelow (f '' Partition.subinterval P i) := hBelow.mono (Set.image_mono (t11_sub_subset P i))
  have : upperStep P f i ≤ lowerStep P f i + eta := by
    unfold upperStep
    refine csSup_le hne ?_
    rintro _ ⟨x, hx, rfl⟩
    have : f x - eta ≤ lowerStep P f i := by
      unfold lowerStep
      refine le_csInf hne ?_
      rintro _ ⟨y, hy, rfl⟩
      have := hosc x hx y hy
      linarith [le_abs_self (f x - f y)]
    linarith
  linarith

theorem t12_sum_adjacent_sub {n : ℕ} (g : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (g i.succ - g i.castSucc)) = g (Fin.last n) - g 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      have htail := ih (fun i : Fin (n + 1) => g i.succ)
      have htail' :
          (∑ i : Fin n, (g i.succ.succ - g i.succ.castSucc)) =
            g (Fin.last n).succ - g (Fin.succ 0) := by
        simpa only [Fin.succ_castSucc] using htail
      rw [htail']
      simp

theorem t12_sum_incr {f α : ℝ → ℝ} {a b : ℝ} (P : Partition a b) :
    (∑ i : Fin P.n, (α (P.pts i.succ) - α (P.pts i.castSucc))) = α b - α a := by
  have := t12_sum_adjacent_sub (fun j => α (P.pts j))
  rw [this, P.pts_end, P.pts_start]

theorem sol_partitionOscillation_le_two_mul_bound_alpha_span
    {f α : ℝ → ℝ} {a b C : ℝ}
    (hs : SourceHypotheses a b f α)
    (P : Partition a b)
    (hC : ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C) :
    partitionOscillation P f α ≤ 2 * C * (α b - α a) := by
  rw [← t12_sum_incr (f := f) P, Finset.mul_sum]
  unfold partitionOscillation
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_right
    (sol_upperStep_sub_lowerStep_le_two_mul_abs_bound P i hs.2.1 hs.2.2.1 hC)
    (t11_incr_nonneg hs P i)

theorem sol_partitionOscillation_le_good_bad_split
    {f α : ℝ → ℝ} {a b C eta : ℝ}
    (hs : SourceHypotheses a b f α)
    (P : Partition a b)
    (B : Finset ℕ)
    (heta_nonneg : 0 ≤ eta)
    (hgood :
      ∀ i : Fin P.n, i.val ∉ B →
        upperStep P f i - lowerStep P f i ≤ eta)
    (hbad :
      ∀ i : Fin P.n, i.val ∈ B →
        upperStep P f i - lowerStep P f i ≤ 2 * C) :
    partitionOscillation P f α ≤
      eta * (α b - α a) +
        2 * C *
          (∑ i ∈ (Finset.univ : Finset (Fin P.n)).filter (fun i => i.val ∈ B),
            (α (P.pts i.succ) - α (P.pts i.castSucc))) := by
  classical
  rw [← t12_sum_incr (f := f) P, Finset.mul_sum, Finset.mul_sum, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  unfold partitionOscillation
  refine Finset.sum_le_sum fun i _ => ?_
  have hw := t11_incr_nonneg hs P i
  have he : 0 ≤ eta * (α (P.pts i.succ) - α (P.pts i.castSucc)) := mul_nonneg heta_nonneg hw
  by_cases hi : i.val ∈ B
  · rw [if_pos hi]
    have := mul_le_mul_of_nonneg_right (hbad i hi) hw
    linarith
  · rw [if_neg hi]
    have := mul_le_mul_of_nonneg_right (hgood i hi) hw
    linarith

theorem sol_partition_cell_endpoints_abs_lt_of_meets_half_radius
    {a b c r : ℝ} (P : Partition a b) {i : Fin P.n}
    (_hr : 0 < r)
    (hmesh : P.mesh < r / 2)
    {x : ℝ} (hxcell : x ∈ Partition.subinterval P i)
    (hxclose : |x - c| < r / 2) :
    |P.pts i.castSucc - c| < r ∧ |P.pts i.succ - c| < r := by
  have hlen : P.pts i.succ - P.pts i.castSucc ≤ P.mesh := by
    unfold Partition.mesh
    exact Finset.le_sup' (fun i : Fin P.n => P.pts i.succ - P.pts i.castSucc) (Finset.mem_univ i)
  obtain ⟨h1, h2⟩ := hxcell
  rw [abs_lt] at hxclose ⊢
  rw [abs_lt]
  constructor <;> constructor <;> linarith [hxclose.1, hxclose.2]

theorem sol_badPointEndpointBlock_disjoint_of_disjoint_Ioo {a b c d r s : ℝ}
    (P : Partition a b)
    (hsep :
      Disjoint (Set.Ioo (c - r) (c + r)) (Set.Ioo (d - s) (d + s))) :
    Disjoint (badPointEndpointBlock P c r) (badPointEndpointBlock P d s) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiC hiD
  unfold badPointEndpointBlock at hiC hiD
  rw [Finset.mem_filter, Finset.mem_range] at hiC hiD
  obtain ⟨hi, hC1, hC2⟩ := hiC
  obtain ⟨_, hD1, hD2⟩ := hiD
  have e1 : i ≤ P.n := hi.le
  have e2 : i + 1 ≤ P.n := hi
  change c - r < (if h : i ≤ P.n then P.pts ⟨i, Nat.lt_succ_iff.mpr h⟩ else b) at hC1
  change (if h : i + 1 ≤ P.n then P.pts ⟨i + 1, Nat.lt_succ_iff.mpr h⟩ else b) < c + r at hC2
  change d - s < (if h : i ≤ P.n then P.pts ⟨i, Nat.lt_succ_iff.mpr h⟩ else b) at hD1
  change (if h : i + 1 ≤ P.n then P.pts ⟨i + 1, Nat.lt_succ_iff.mpr h⟩ else b) < d + s at hD2
  rw [dif_pos e1] at hC1 hD1
  rw [dif_pos e2] at hC2 hD2
  have hstep : P.pts ⟨i, Nat.lt_succ_iff.mpr e1⟩ < P.pts ⟨i + 1, Nat.lt_succ_iff.mpr e2⟩ :=
    P.strict_mono (by simp [Fin.lt_def])
  exact Set.disjoint_left.mp hsep ⟨hC1, hstep.trans hC2⟩ ⟨hD1, hstep.trans hD2⟩

theorem sol_badPointEndpointBlock_subset_canonical_Ico {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    badPointEndpointBlock P c r ⊆
      Finset.Ico (badPointCanonicalLo P c r) (badPointCanonicalHi P c r) := by
  classical
  intro i hiC
  unfold badPointEndpointBlock at hiC
  rw [Finset.mem_filter, Finset.mem_range] at hiC
  obtain ⟨hi, hC1, hC2⟩ := hiC
  have hL : i ∈ badPointLeftCutCandidates P c r := by
    unfold badPointLeftCutCandidates
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hC1.le⟩
  have hR : i + 1 ∈ badPointRightCutCandidates P c r := by
    unfold badPointRightCutCandidates
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hC2.le⟩
  rw [Finset.mem_Ico]
  exact ⟨badPointCanonicalLo_le_of_mem_leftCandidates P hcI hr hL,
    le_badPointCanonicalHi_of_mem_rightCandidates P hcI hr hR⟩

theorem sol_closedIntervalDarbouxGapSmall_of_oscillationSmall
    {f α : ℝ → ℝ} {a b : ℝ}
    (hosc : ClosedIntervalDarbouxOscillationSmall a b f α) :
    ClosedIntervalDarbouxGapSmall a b f α := by
  intro eps he
  obtain ⟨δ, hδ, h⟩ := hosc eps he
  exact ⟨δ, hδ, fun P hP => by rw [sol_upperSum_sub_lowerSum_eq_partitionOscillation]; exact h P hP⟩

theorem sol_partition_cell_increment_le_bad_interval
    {α : ℝ → ℝ} {a b c r : ℝ}
    (hα_mono : Monotone α)
    (P : Partition a b) {i : Fin P.n}
    (hleft : |P.pts i.castSucc - c| < r)
    (hright : |P.pts i.succ - c| < r) :
    α (P.pts i.succ) - α (P.pts i.castSucc) ≤ α (c + r) - α (c - r) := by
  rw [abs_lt] at hleft hright
  have h1 := hα_mono (show P.pts i.succ ≤ c + r by linarith)
  have h2 := hα_mono (show c - r ≤ P.pts i.castSucc by linarith)
  linarith

theorem sol_partition_cell_increment_le_bad_interval_of_half_radius_hit
    {α : ℝ → ℝ} {a b c r : ℝ}
    (hα_mono : Monotone α)
    (P : Partition a b) {i : Fin P.n}
    (hr : 0 < r)
    (hmesh : P.mesh < r / 2)
    {x : ℝ} (hxcell : x ∈ Partition.subinterval P i)
    (hxclose : |x - c| < r / 2) :
    α (P.pts i.succ) - α (P.pts i.castSucc) ≤ α (c + r) - α (c - r) := by
  obtain ⟨h1, h2⟩ := sol_partition_cell_endpoints_abs_lt_of_meets_half_radius P hr hmesh hxcell hxclose
  exact sol_partition_cell_increment_le_bad_interval hα_mono P h1 h2

def t13_pan {a b : ℝ} (P : Partition a b) (j : ℕ) : ℝ :=
  if h : j ≤ P.n then P.pts ⟨j, Nat.lt_succ_iff.mpr h⟩ else b

theorem t13_pan_cs {a b : ℝ} (P : Partition a b) {i : ℕ} (hi : i < P.n) :
    t13_pan P i = P.pts (Fin.castSucc ⟨i, hi⟩) := by
  unfold t13_pan; rw [dif_pos hi.le]; rfl

theorem t13_pan_s {a b : ℝ} (P : Partition a b) {i : ℕ} (hi : i < P.n) :
    t13_pan P (i + 1) = P.pts (Fin.succ ⟨i, hi⟩) := by
  unfold t13_pan; rw [dif_pos (show i + 1 ≤ P.n from hi)]; rfl

theorem t13_pan_mono {a b : ℝ} (P : Partition a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ P.n) :
    t13_pan P i ≤ t13_pan P j := by
  unfold t13_pan
  rw [dif_pos (hij.trans hj), dif_pos hj]
  exact P.strict_mono.monotone (by simp [Fin.le_def, hij])

theorem t13_pan_lt {a b : ℝ} (P : Partition a b) {i : ℕ} (hi : i < P.n) :
    t13_pan P i < t13_pan P (i + 1) := by
  rw [t13_pan_cs P hi, t13_pan_s P hi]
  exact P.strict_mono Fin.castSucc_lt_succ

theorem sol_badCellIndices_half_radius_subset_badPointEndpointBlocks {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hmesh : ∀ c : ℝ, c ∈ S → P.mesh < rho c / 2) :
    badCellIndices P S (fun c : ℝ => rho c / 2) ⊆
      S.biUnion (fun c : ℝ => badPointEndpointBlock P c (rho c)) := by
  classical
  intro i hi
  obtain ⟨c, hc, x, hi', hx, hxc⟩ := sol_exists_bad_point_of_mem_badCellIndices P S _ hi
  obtain ⟨h1, h2⟩ := sol_partition_cell_endpoints_abs_lt_of_meets_half_radius P (hrho_pos c hc)
    (hmesh c hc) hx hxc
  rw [Finset.mem_biUnion]
  refine ⟨c, hc, ?_⟩
  unfold badPointEndpointBlock
  rw [Finset.mem_filter, Finset.mem_range]
  change i < P.n ∧ c - rho c < t13_pan P i ∧ t13_pan P (i + 1) < c + rho c
  rw [t13_pan_cs P hi', t13_pan_s P hi']
  rw [abs_lt] at h1 h2
  exact ⟨hi', by linarith, by linarith⟩

theorem sol_badPointCanonicalIcoBlocks_pairwiseDisjoint_of_pairwiseDisjoint_Ioo
    {a b : ℝ} (P : Partition a b)
    (S : Finset ℝ) (rho : ℝ → ℝ)
    (hcI : ∀ c : ℝ, c ∈ S → c ∈ Icc a b)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hsep :
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c))) :
    (↑S : Set ℝ).PairwiseDisjoint
      (fun c : ℝ =>
        Finset.Ico (badPointCanonicalLo P c (rho c))
          (badPointCanonicalHi P c (rho c))) := by
  classical
  have key : ∀ c : ℝ, c ∈ S → ∀ k, k ∈ Finset.Ico (badPointCanonicalLo P c (rho c))
      (badPointCanonicalHi P c (rho c)) →
      k < P.n ∧ c - rho c ≤ t13_pan P k ∧ t13_pan P (k + 1) ≤ c + rho c := by
    intro c hc k hk
    rw [Finset.mem_Ico] at hk
    have hL := badPointCanonicalLo_mem_leftCandidates P (hcI c hc) (hrho_pos c hc)
    have hR := badPointCanonicalHi_mem_rightCandidates P (hcI c hc) (hrho_pos c hc)
    unfold badPointLeftCutCandidates at hL
    unfold badPointRightCutCandidates at hR
    rw [Finset.mem_filter, Finset.mem_range] at hL hR
    change _ ∧ c - rho c ≤ t13_pan P _ at hL
    change _ ∧ t13_pan P _ ≤ c + rho c at hR
    have hkn : k < P.n := by omega
    refine ⟨hkn, ?_, ?_⟩
    · exact hL.2.trans (t13_pan_mono P hk.1 hkn.le)
    · exact (t13_pan_mono P (show k + 1 ≤ badPointCanonicalHi P c (rho c) by omega) (by omega)).trans hR.2
  intro c hc d hd hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro k hk1 hk2
  obtain ⟨hkn, c1, c2⟩ := key c hc k hk1
  obtain ⟨_, d1, d2⟩ := key d hd k hk2
  have hlt := t13_pan_lt P hkn
  set m := (t13_pan P k + t13_pan P (k + 1)) / 2
  have hmc : m ∈ Set.Ioo (c - rho c) (c + rho c) := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  have hmd : m ∈ Set.Ioo (d - rho d) (d + rho d) := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  exact Set.disjoint_left.mp (hsep hc hd hne) hmc hmd

theorem sol_exists_upperStep_sub_lowerStep_lt_of_goodRemainder_cell
    {f : ℝ → ℝ} {a b eta : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ}
    (hS : ∀ x : ℝ, x ∈ S ↔ x ∈ discontinuitySetOn f a b)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (P : Partition a b) (i : Fin P.n),
        P.mesh < delta →
        Partition.subinterval P i ⊆ goodRemainder a b S rho →
          upperStep P f i - lowerStep P f i < eta := by
  have huc := (sol_isCompact_goodRemainder (a := a) (b := b) (S := S) (rho := rho)).uniformContinuousOn_of_continuous
    (sol_continuousOn_goodRemainder hS hrho_pos)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, h⟩ := huc (eta / 2) (by linarith)
  refine ⟨δ, hδ, fun P i hP hsub => ?_⟩
  have hlen : P.pts i.succ - P.pts i.castSucc ≤ P.mesh := by
    unfold Partition.mesh
    exact Finset.le_sup' (fun i : Fin P.n => P.pts i.succ - P.pts i.castSucc) (Finset.mem_univ i)
  have := sol_upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound (eta := eta / 2) P i hAbove hBelow
    (fun x hx y hy => by
      have hd : dist x y < δ := by
        rw [Real.dist_eq]
        linarith [abs_sub_le_cell_length_of_mem_subinterval P hx hy]
      have := h x (hsub hx) y (hsub hy) hd
      rw [Real.dist_eq] at this
      exact this.le)
  linarith

theorem sol_strict_common_limit_criterion_of_upperLower_criterion
    (hULcriterion : StrictFiniteDiscontinuityUpperLowerCriterion) :
    StrictFiniteDiscontinuityCommonLimitCriterion := by
  intro f α a b hab hm hA hB hD hC
  obtain ⟨L, hL⟩ := hULcriterion hab hm hA hB hD hC
  have hL' : UpperLowerCommonLimit a b f α L := hL
  obtain ⟨hs, hlim⟩ := hL'
  refine ⟨L, hL, ?_⟩
  show TaggedCommonLimit a b f α L
  refine ⟨hs, fun eps he => ?_⟩
  obtain ⟨δ, hδ, h⟩ := hlim eps he
  refine ⟨δ, hδ, fun P tags ht hP => ?_⟩
  have lo : lowerSum P f α ≤ taggedSum P tags f α := by
    unfold lowerSum taggedSum
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (t11_incr_nonneg hs P i)
    unfold lowerStep
    exact csInf_le (hB.mono (Set.image_mono (t11_sub_subset P i))) (Set.mem_image_of_mem f (ht i))
  have up : taggedSum P tags f α ≤ upperSum P f α := by
    unfold upperSum taggedSum
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (t11_incr_nonneg hs P i)
    unfold upperStep
    exact le_csSup (hA.mono (Set.image_mono (t11_sub_subset P i))) (Set.mem_image_of_mem f (ht i))
  obtain ⟨h1, h2⟩ := h P hP
  rw [abs_lt] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem t14_mesh_small {a b : ℝ} (hab : a < b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, (uniformPartition a b hab (n + 1) (Nat.succ_pos n)).mesh < δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  refine ⟨N, fun n hn => ?_⟩
  rw [uniformPartition_mesh_eq]
  have hn' : ((b - a) / δ) < (n : ℝ) + 1 := by
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [div_lt_iff₀ hδ] at hn'
  push_cast
  rw [div_lt_iff₀ (by positivity)]
  linarith

theorem sol_closedIntervalDarbouxCommonLimit_of_fineCauchy
    {f α : ℝ → ℝ} {a b : ℝ}
    (hs : SourceHypotheses a b f α)
    (hfine : ClosedIntervalDarbouxFineCauchy a b f α) :
    ∃ L, rsUpperLowerCommonLimit a b f α L := by
  have hab := hs.1
  set u : ℕ → ℝ := fun n => upperSum (uniformPartition a b hab (n + 1) (Nat.succ_pos n)) f α with hu
  have hcau : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hfine ε hε
    obtain ⟨N, hN⟩ := t14_mesh_small hab hδ
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [Real.dist_eq]
    exact (h _ _ (hN m hm) (hN n hn)).1
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨L, hs, fun eps he => ?_⟩
  obtain ⟨δ, hδ, h⟩ := hfine (eps / 2) (by linarith)
  refine ⟨δ, hδ, fun P hP => ?_⟩
  obtain ⟨N, hN⟩ := t14_mesh_small hab hδ
  have hev := (Metric.tendsto_atTop.1 hL) (eps / 2) (by linarith)
  obtain ⟨M, hM⟩ := hev
  set n := max N M
  have h1 := hM n (le_max_right _ _)
  rw [Real.dist_eq] at h1
  obtain ⟨k1, _, _, k4⟩ := h P _ hP (hN n (le_max_left _ _))
  have k1' : |upperSum P f α - u n| < eps / 2 := k1
  have k4' : |lowerSum P f α - u n| < eps / 2 := k4
  rw [abs_lt] at h1 k1' k4' ⊢
  rw [abs_lt]
  constructor <;> constructor <;> linarith [h1.1, h1.2, k1'.1, k1'.2, k4'.1, k4'.2]

theorem sol_closedIntervalDarbouxCommonLimitFromGap_of_fineCauchy
    (hfine : ClosedIntervalDarbouxFineCauchyFromGap) :
    ClosedIntervalDarbouxCommonLimitFromGap := by
  intro f α a b hs hgap
  exact sol_closedIntervalDarbouxCommonLimit_of_fineCauchy hs (hfine hs hgap)

theorem sol_finite_discontinuity_alpha_local_increment_data
    {f α : ℝ → ℝ} {a b eps : ℝ}
    (hDiscFinite : (discontinuitySetOn f a b).Finite)
    (hαCont :
      ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x)
    (heps : 0 < eps) :
    ∃ S : Finset ℝ,
      (∀ x : ℝ, x ∈ S ↔ x ∈ discontinuitySetOn f a b) ∧
      ∃ rho : ℝ → ℝ,
        (∀ c : ℝ, c ∈ S → 0 < rho c) ∧
        (∑ c ∈ S, (α (c + rho c) - α (c - rho c))) < eps := by
  classical
  set S := hDiscFinite.toFinset with hSdef
  have hmem : ∀ x : ℝ, x ∈ S ↔ x ∈ discontinuitySetOn f a b := fun x => Set.Finite.mem_toFinset _
  set e' : ℝ := eps / (S.card + 1) with he'
  have he'pos : 0 < e' := by positivity
  have hloc : ∀ c ∈ S, ∃ r : ℝ, 0 < r ∧ α (c + r) - α (c - r) < e' := by
    intro c hc
    have hca := hαCont ((hmem c).1 hc)
    rw [Metric.continuousAt_iff] at hca
    obtain ⟨δ, hδ, h⟩ := hca (e' / 2) (by linarith)
    refine ⟨δ / 2, by linarith, ?_⟩
    have h1 := h (x := c + δ / 2) (by rw [Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
    have h2 := h (x := c - δ / 2) (by rw [Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq, abs_lt] at h1 h2
    linarith [h1.1, h1.2, h2.1, h2.2]
  choose! rho hpos hlt using hloc
  refine ⟨S, hmem, rho, hpos, ?_⟩
  have hle : (∑ c ∈ S, (α (c + rho c) - α (c - rho c))) ≤ S.card * e' := by
    have := Finset.sum_le_card_nsmul S (fun c => α (c + rho c) - α (c - rho c)) e'
      (fun c hc => (hlt c hc).le)
    simpa [nsmul_eq_mul] using this
  have hlt2 : (S.card : ℝ) * e' < eps := by
    rw [he', mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

theorem solution
    {f α : ℝ → ℝ} {a b eps : ℝ}
    (hDiscFinite : (discontinuitySetOn f a b).Finite)
    (hαCont :
      ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x)
    (heps : 0 < eps) :
    ∃ S : Finset ℝ,
      (∀ x : ℝ, x ∈ S ↔ x ∈ discontinuitySetOn f a b) ∧
      ∃ rho : ℝ → ℝ,
        (∀ c : ℝ, c ∈ S → 0 < rho c) ∧
        (∑ c ∈ S, (α (c + rho c) - α (c - rho c))) < eps := by
  apply sol_finite_discontinuity_alpha_local_increment_data <;> assumption
