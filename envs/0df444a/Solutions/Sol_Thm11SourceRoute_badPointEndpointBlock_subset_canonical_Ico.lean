-- Prove2me | solution 1 for Thm11SourceRoute.badPointEndpointBlock_subset_canonical_Ico
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T15:32:46.113848+00:00
-- url     : https://prove2.me/submissions/e16f6933-e7ab-4af3-b035-75147f714e03

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F000
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

theorem solution {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    badPointEndpointBlock P c r ⊆
      Finset.Ico (badPointCanonicalLo P c r) (badPointCanonicalHi P c r) := by
  apply sol_badPointEndpointBlock_subset_canonical_Ico <;> assumption
