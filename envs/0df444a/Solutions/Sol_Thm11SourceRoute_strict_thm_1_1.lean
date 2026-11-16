-- Prove2me | solution 1 for Thm11SourceRoute.strict_thm_1_1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T15:42:47.874325+00:00
-- url     : https://prove2.me/submissions/22213507-be47-4a67-87db-fe9182048faf

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F001
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F005
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F006
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F007
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F008
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F001
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_darboux_gap_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_limit_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_limit_F001
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_finite_discontinuity_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_refinement_points_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_refinement_points_F001
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_refinement_monotonicity_F000
import Mathlib.Data.List.GetD
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep
open Finset BigOperators
open Set Topology

namespace DarbouxRS
/--
The integrator function `alpha` does not decrease across any subinterval of the partition.

Because `alpha` is assumed to be monotonic on `[a, b]` (via `SourceHypotheses`), and the
partition points strictly increase (`x_i < x_{i+1}`), the difference `alpha(x_{i+1}) - alpha(x_i)`
is always non-negative. This guarantees that the width/weights in the Riemann-Stieltjes sum
are non-negative.
-/
private lemma partition_increment_nonneg_of_source_core_local {a b : ℝ} (P : Partition a b)
    {f alpha : ℝ → ℝ} (hs : SourceHypotheses a b f alpha) {i : Fin P.n} :
    0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) := by
  -- Unpack the SourceHypotheses to get the monotonicity of alpha
  rcases hs with ⟨_hab, _hAbove, _hBelow, hmono⟩

  -- The endpoints of the subinterval are in [a, b]
  have hleft : P.pts i.castSucc ∈ Set.Icc a b := partition_pts_mem_Icc_core P
  have hright : P.pts i.succ ∈ Set.Icc a b := partition_pts_mem_Icc_core P

  -- Because x_i < x_{i+1}, monotonicity implies alpha(x_i) ≤ alpha(x_{i+1})
  have h_pts_lt : P.pts i.castSucc < P.pts i.succ :=
    P.strict_mono (Fin.castSucc_lt_succ)

  exact sub_nonneg.mpr (hmono hleft hright (le_of_lt h_pts_lt))
end DarbouxRS

namespace Thm11SourceRoute

/-- The partition indices whose cells are not contained in the chosen good
remainder. These are the cells that must be charged to bad-point neighborhoods. -/
private def subintervalAtNat_local {a b : ℝ} (P : Partition a b) (i : ℕ) : Set ℝ :=
  if h : i < P.n then Partition.subinterval P ⟨i, h⟩ else ∅

private lemma mem_badCellIndices_iff_local {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ) {i : ℕ} :
    i ∈ badCellIndices P S rho ↔
      i < P.n ∧
        ∀ hi : i < P.n,
          ¬ Partition.subinterval P ⟨i, hi⟩ ⊆ goodRemainder a b S rho := by
  classical
  rw [badCellIndices, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hi, hbad⟩
    refine ⟨hi, ?_⟩
    intro hi'
    change ¬ subintervalAtNat_local P i ⊆ goodRemainder a b S rho at hbad
    simpa [subintervalAtNat_local, hi'] using hbad
  · rintro ⟨hi, hbad⟩
    refine ⟨hi, ?_⟩
    change ¬ subintervalAtNat_local P i ⊆ goodRemainder a b S rho
    simpa [subintervalAtNat_local, hi] using hbad hi

private lemma cell_subset_goodRemainder_of_not_mem_badCellIndices_local {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ)
    (i : Fin P.n)
    (hi_not_bad : i.val ∉ badCellIndices P S rho) :
    Partition.subinterval P i ⊆ goodRemainder a b S rho := by
  by_contra hnot
  exact hi_not_bad ((mem_badCellIndices_iff_local P S rho).2 ⟨i.isLt, fun _ => hnot⟩)


private def pointAtNat {a b : ℝ} (P : Partition a b) (j : ℕ) : ℝ :=
  if h : j ≤ P.n then P.pts ⟨j, Nat.lt_succ_iff.mpr h⟩ else b
private lemma pointAtNat_eq {a b : ℝ} (P : Partition a b)
    {j : ℕ} (hj : j ≤ P.n) :
    pointAtNat P j = P.pts ⟨j, Nat.lt_succ_iff.mpr hj⟩ := by
  simp [pointAtNat, hj]
private lemma pointAtNat_zero {a b : ℝ} (P : Partition a b) :
    pointAtNat P 0 = a := by
  simp [pointAtNat, P.pts_start]
private lemma pointAtNat_end {a b : ℝ} (P : Partition a b) :
    pointAtNat P P.n = b := by
  rw [pointAtNat_eq P (le_refl P.n)]
  convert P.pts_end using 1
  congr 1
private lemma pointAtNat_mono {a b : ℝ} (P : Partition a b)
    {i j : ℕ} (hi : i ≤ P.n) (hj : j ≤ P.n) (hij : i ≤ j) :
    pointAtNat P i ≤ pointAtNat P j := by
  rw [pointAtNat_eq P hi, pointAtNat_eq P hj]
  exact DarbouxRS.partition_pts_monotone_core P (by exact_mod_cast hij)
private lemma pointAtNat_strictMono {a b : ℝ} (P : Partition a b)
    {i j : ℕ} (hi : i ≤ P.n) (hj : j ≤ P.n) (hij : i < j) :
    pointAtNat P i < pointAtNat P j := by
  rw [pointAtNat_eq P hi, pointAtNat_eq P hj]
  exact P.strict_mono (by exact_mod_cast hij)
private lemma badPointCanonicalLo_left_bound {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    c - r ≤ pointAtNat P (badPointCanonicalLo P c r) := by
  have hmem := badPointCanonicalLo_mem_leftCandidates P hcI hr
  rw [badPointLeftCutCandidates] at hmem
  exact (Finset.mem_filter.mp hmem).2
private lemma badPointCanonicalHi_right_bound {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    pointAtNat P (badPointCanonicalHi P c r) ≤ c + r := by
  have hmem := badPointCanonicalHi_mem_rightCandidates P hcI hr
  rw [badPointRightCutCandidates] at hmem
  exact (Finset.mem_filter.mp hmem).2

private lemma mem_badPointEndpointBlock_iff_local {a b c r : ℝ}
    (P : Partition a b) {i : ℕ} :
    i ∈ badPointEndpointBlock P c r ↔
      i < P.n ∧ c - r < pointAtNat P i ∧ pointAtNat P (i + 1) < c + r := by
  classical
  simp only [badPointEndpointBlock, Finset.mem_filter, Finset.mem_range] <;> rfl

/-- The endpoint-selected bad cells around `c` are covered by the canonical
consecutive block cut out by the first left and last right partition cutpoints. -/
private lemma badPointEndpointBlock_subset_canonical_Ico_local {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    badPointEndpointBlock P c r ⊆
      Finset.Ico (badPointCanonicalLo P c r) (badPointCanonicalHi P c r) := by
  intro i hi_block
  rw [mem_badPointEndpointBlock_iff_local P] at hi_block
  have hi_left : i ∈ badPointLeftCutCandidates P c r := by
    rw [badPointLeftCutCandidates]
    refine Finset.mem_filter.mpr ⟨?_, le_of_lt hi_block.2.1⟩
    exact Finset.mem_range.mpr (Nat.lt_trans hi_block.1 (Nat.lt_succ_self P.n))
  have hi_right : i + 1 ∈ badPointRightCutCandidates P c r := by
    rw [badPointRightCutCandidates]
    refine Finset.mem_filter.mpr ⟨?_, le_of_lt hi_block.2.2⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.succ_le_of_lt hi_block.1))
  rw [Finset.mem_Ico]
  exact ⟨badPointCanonicalLo_le_of_mem_leftCandidates P hcI hr hi_left,
    Nat.lt_of_succ_le
      (le_badPointCanonicalHi_of_mem_rightCandidates P hcI hr hi_right)⟩

private lemma mem_goodRemainder_iff_local {a b x : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ} :
    x ∈ goodRemainder a b S rho ↔
      x ∈ Icc a b ∧ ∀ c : ℝ, c ∈ S → rho c ≤ |x - c| := by
  simp [goodRemainder]

/-- Any two points in one partition cell are separated by at most that cell's
length. -/
private lemma abs_sub_le_cell_length_of_mem_subinterval_local {a b x y : ℝ}
    (P : Partition a b) {i : Fin P.n}
    (hx : x ∈ Partition.subinterval P i)
    (hy : y ∈ Partition.subinterval P i) :
    |x - y| ≤ P.pts i.succ - P.pts i.castSucc := by
  rcases hx with ⟨hix, hxi⟩
  rcases hy with ⟨hiy, hyi⟩
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith

/-- If a partition cell is not contained in the good remainder, then it meets
one of the removed bad-point balls. -/
private lemma exists_bad_point_of_not_subset_goodRemainder_cell_local
    {a b : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ}
    (P : Partition a b) {i : Fin P.n}
    (hcell_not_good :
      ¬ Partition.subinterval P i ⊆ goodRemainder a b S rho) :
    ∃ c : ℝ, c ∈ S ∧ ∃ x : ℝ,
      x ∈ Partition.subinterval P i ∧ |x - c| < rho c := by
  rw [Set.not_subset] at hcell_not_good
  rcases hcell_not_good with ⟨x, hxcell, hxnotgood⟩
  have hxI : x ∈ Icc a b :=
    DarbouxRS.subinterval_subset_Icc_core P hxcell
  rw [mem_goodRemainder_iff_local] at hxnotgood
  have hnot_all : ¬ ∀ c : ℝ, c ∈ S → rho c ≤ |x - c| := by
    intro hall
    exact hxnotgood ⟨hxI, hall⟩
  push Not at hnot_all
  rcases hnot_all with ⟨c, hcS, hclose⟩
  exact ⟨c, hcS, x, hxcell, hclose⟩

/-- A bad cell for the half-radius good remainder meets a half-radius bad ball. -/
private lemma exists_bad_point_half_radius_of_not_subset_goodRemainder_cell_local
    {a b : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ}
    (P : Partition a b) {i : Fin P.n}
    (hcell_not_good :
      ¬ Partition.subinterval P i ⊆
        goodRemainder a b S (fun c : ℝ => rho c / 2)) :
    ∃ c : ℝ, c ∈ S ∧ ∃ x : ℝ,
      x ∈ Partition.subinterval P i ∧ |x - c| < rho c / 2 :=
  exists_bad_point_of_not_subset_goodRemainder_cell_local P hcell_not_good

/-- If a cell meets the half-radius ball around `c` and the mesh is below that
half-radius, then both cell endpoints lie in the full-radius ball around `c`. -/
private lemma partition_cell_endpoints_abs_lt_of_meets_half_radius_local
    {a b c r : ℝ} (P : Partition a b) {i : Fin P.n}
    (_hr : 0 < r)
    (hmesh : P.mesh < r / 2)
    {x : ℝ} (hxcell : x ∈ Partition.subinterval P i)
    (hxclose : |x - c| < r / 2) :
    |P.pts i.castSucc - c| < r ∧ |P.pts i.succ - c| < r := by
  have hleft_mem : P.pts i.castSucc ∈ Partition.subinterval P i :=
    ⟨le_rfl, le_of_lt (P.strict_mono Fin.castSucc_lt_succ)⟩
  have hright_mem : P.pts i.succ ∈ Partition.subinterval P i :=
    ⟨le_of_lt (P.strict_mono Fin.castSucc_lt_succ), le_rfl⟩
  have hleft_len :
      |P.pts i.castSucc - x| ≤ P.pts i.succ - P.pts i.castSucc :=
    abs_sub_le_cell_length_of_mem_subinterval_local P hleft_mem hxcell
  have hright_len :
      |P.pts i.succ - x| ≤ P.pts i.succ - P.pts i.castSucc :=
    abs_sub_le_cell_length_of_mem_subinterval_local P hright_mem hxcell
  have hlen_mesh : P.pts i.succ - P.pts i.castSucc ≤ P.mesh := by
    unfold Partition.mesh
    exact Finset.le_sup'
      (fun j : Fin P.n => P.pts j.succ - P.pts j.castSucc)
      (Finset.mem_univ i)
  have hleft_close : |P.pts i.castSucc - x| < r / 2 :=
    lt_of_le_of_lt (le_trans hleft_len hlen_mesh) hmesh
  have hright_close : |P.pts i.succ - x| < r / 2 :=
    lt_of_le_of_lt (le_trans hright_len hlen_mesh) hmesh
  have hleft_tri :
      |P.pts i.castSucc - c| ≤ |P.pts i.castSucc - x| + |x - c| := by
    have hdecomp : P.pts i.castSucc - c = (P.pts i.castSucc - x) + (x - c) := by ring
    rw [hdecomp]
    exact abs_add_le _ _
  have hright_tri :
      |P.pts i.succ - c| ≤ |P.pts i.succ - x| + |x - c| := by
    have hdecomp : P.pts i.succ - c =
        (P.pts i.succ - x) + (x - c) := by ring
    rw [hdecomp]
    exact abs_add_le _ _
  constructor <;> linarith

/-- With mesh below every half-radius, each half-radius bad cell is covered by
the endpoint block of some bad point. -/
private lemma badCellIndices_half_radius_subset_badPointEndpointBlocks_local {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hmesh : ∀ c : ℝ, c ∈ S → P.mesh < rho c / 2) :
    badCellIndices P S (fun c : ℝ => rho c / 2) ⊆
      S.biUnion (fun c : ℝ => badPointEndpointBlock P c (rho c)) := by
  classical
  intro i hi_bad
  rcases (mem_badCellIndices_iff_local P S (fun c : ℝ => rho c / 2)).1 hi_bad with
    ⟨hi, hnot_good⟩
  rcases exists_bad_point_half_radius_of_not_subset_goodRemainder_cell_local
      P (hnot_good hi) with
    ⟨c, hcS, x, hxcell, hxclose⟩
  rcases partition_cell_endpoints_abs_lt_of_meets_half_radius_local
      P (hrho_pos c hcS) (hmesh c hcS) hxcell hxclose with
    ⟨hleft_abs, hright_abs⟩
  refine Finset.mem_biUnion.mpr ⟨c, hcS, ?_⟩
  rw [mem_badPointEndpointBlock_iff_local P]
  refine ⟨hi, ?_, ?_⟩
  · have hleft_abs' : |pointAtNat P i - c| < rho c := by
      rw [pointAtNat_eq P (Nat.le_of_lt hi)]
      simpa using hleft_abs
    have hleft := (abs_lt.mp hleft_abs').1
    linarith
  · have hright_abs' : |pointAtNat P (i + 1) - c| < rho c := by
      rw [pointAtNat_eq P (Nat.succ_le_of_lt hi)]
      simpa using hright_abs
    have hright := (abs_lt.mp hright_abs').2
    linarith

/-- Pairwise-disjoint bad-point intervals induce pairwise-disjoint canonical
consecutive partition-index blocks. -/
private lemma badPointCanonicalIcoBlocks_pairwiseDisjoint_of_pairwiseDisjoint_Ioo_local
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
  rw [Set.PairwiseDisjoint] at hsep ⊢
  intro c hc d hd hne
  change Disjoint
    (Finset.Ico (badPointCanonicalLo P c (rho c))
      (badPointCanonicalHi P c (rho c)))
    (Finset.Ico (badPointCanonicalLo P d (rho d))
      (badPointCanonicalHi P d (rho d)))
  rw [Finset.disjoint_left]
  intro i hiC hiD
  rw [Finset.mem_Ico] at hiC hiD
  have hhiC_le_n := badPointCanonicalHi_le_n P (hcI c hc) (hrho_pos c hc)
  have hhiD_le_n := badPointCanonicalHi_le_n P (hcI d hd) (hrho_pos d hd)
  have hi_lt_n : i < P.n := lt_of_lt_of_le hiC.2 hhiC_le_n
  have hstep : pointAtNat P i < pointAtNat P (i + 1) :=
    pointAtNat_strictMono P (Nat.le_of_lt hi_lt_n) (Nat.succ_le_of_lt hi_lt_n) (by omega)
  let y : ℝ := (pointAtNat P i + pointAtNat P (i + 1)) / 2
  have hleftC : c - rho c ≤ pointAtNat P i := by
    exact le_trans
      (badPointCanonicalLo_left_bound P (hcI c hc) (hrho_pos c hc))
      (pointAtNat_mono P
        (badPointCanonicalLo_le_n P (hcI c hc) (hrho_pos c hc))
        (Nat.le_of_lt hi_lt_n) hiC.1)
  have hrightC : pointAtNat P (i + 1) ≤ c + rho c := by
    exact le_trans
      (pointAtNat_mono P (Nat.succ_le_of_lt hi_lt_n) hhiC_le_n
        (Nat.succ_le_of_lt hiC.2))
      (badPointCanonicalHi_right_bound P (hcI c hc) (hrho_pos c hc))
  have hleftD : d - rho d ≤ pointAtNat P i := by
    exact le_trans
      (badPointCanonicalLo_left_bound P (hcI d hd) (hrho_pos d hd))
      (pointAtNat_mono P
        (badPointCanonicalLo_le_n P (hcI d hd) (hrho_pos d hd))
        (Nat.le_of_lt hi_lt_n) hiD.1)
  have hrightD : pointAtNat P (i + 1) ≤ d + rho d := by
    exact le_trans
      (pointAtNat_mono P (Nat.succ_le_of_lt hi_lt_n) hhiD_le_n
        (Nat.succ_le_of_lt hiD.2))
      (badPointCanonicalHi_right_bound P (hcI d hd) (hrho_pos d hd))
  have hy_left : pointAtNat P i < y := by
    dsimp [y]
    linarith
  have hy_right : y < pointAtNat P (i + 1) := by
    dsimp [y]
    linarith
  have hyC : y ∈ Set.Ioo (c - rho c) (c + rho c) :=
    ⟨lt_of_le_of_lt hleftC hy_left, lt_of_lt_of_le hy_right hrightC⟩
  have hyD : y ∈ Set.Ioo (d - rho d) (d + rho d) :=
    ⟨lt_of_le_of_lt hleftD hy_left, lt_of_lt_of_le hy_right hrightD⟩
  have hempty :
      Set.Ioo (c - rho c) (c + rho c) ∩
          Set.Ioo (d - rho d) (d + rho d) = (∅ : Set ℝ) :=
    Set.disjoint_iff_inter_eq_empty.mp (hsep hc hd hne)
  have hyempty : y ∈ (∅ : Set ℝ) := by
    simpa [hempty] using
      (show y ∈
          Set.Ioo (c - rho c) (c + rho c) ∩
            Set.Ioo (d - rho d) (d + rho d) from
        ⟨hyC, hyD⟩)
  exact hyempty

/-- If all values of `f` on a partition cell differ by at most `eta`, then
the cell upper-minus-lower step is at most `eta`. -/
private lemma upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound_local
    {f : ℝ → ℝ} {a b eta : ℝ}
    (P : Partition a b) (i : Fin P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hosc :
      ∀ x, x ∈ Partition.subinterval P i →
      ∀ y, y ∈ Partition.subinterval P i → |f x - f y| ≤ eta) :
    upperStep P f i - lowerStep P f i ≤ eta := by
  let cell := Partition.subinterval P i
  have hcell_nonempty : (f '' cell).Nonempty := by
    refine ⟨f (P.pts i.castSucc), ?_⟩
    refine ⟨P.pts i.castSucc, ?_, rfl⟩
    exact ⟨le_rfl, le_of_lt (P.strict_mono Fin.castSucc_lt_succ)⟩
  have hcellAbove : BddAbove (f '' cell) :=
    BddAbove.mono (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P)) hAbove
  have hcellBelow : BddBelow (f '' cell) :=
    BddBelow.mono (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P)) hBelow
  have hsup_le :
      sSup (f '' cell) ≤ sInf (f '' cell) + eta := by
    refine csSup_le hcell_nonempty ?_
    rintro _ ⟨x, hx, rfl⟩
    have hle_inf : f x - eta ≤ sInf (f '' cell) := by
      refine le_csInf hcell_nonempty ?_
      rintro _ ⟨y, hy, rfl⟩
      have hxy : f x - f y ≤ eta := (abs_le.mp (hosc x hx y hy)).2
      linarith
    linarith
  unfold upperStep lowerStep
  linarith

/-- A uniform absolute-value bound on `[a,b]` gives a coarse cell oscillation
bound. This is the estimate used for cells near discontinuities. -/
private lemma upperStep_sub_lowerStep_le_two_mul_abs_bound_local
    {f : ℝ → ℝ} {a b C : ℝ}
    (P : Partition a b) (i : Fin P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hC : ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C) :
    upperStep P f i - lowerStep P f i ≤ 2 * C := by
  refine upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound_local
    P i hAbove hBelow ?_
  intro x hx y hy
  have hxI : x ∈ Icc a b := DarbouxRS.subinterval_subset_Icc_core P hx
  have hyI : y ∈ Icc a b := DarbouxRS.subinterval_subset_Icc_core P hy
  have hxC := hC x hxI
  have hyC := hC y hyI
  have htri : |f x - f y| ≤ |f x| + |f y| := by
    calc
      |f x - f y| = |f x + -f y| := by ring_nf
      _ ≤ |f x| + |-f y| := abs_add_le (f x) (-f y)
      _ = |f x| + |f y| := by rw [abs_neg]
  linarith

private lemma sum_adjacent_sub_local {n : ℕ} (g : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (g i.succ - g i.castSucc)) =
      g (Fin.last n) - g 0 := by
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

/-- Split the partition oscillation into a small good-cell contribution plus
a coarse bad-cell contribution supported on a chosen finite index set. -/
private lemma partitionOscillation_le_good_bad_split_local
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
  rcases hs with ⟨hab, hAbove, hBelow, hmono⟩
  unfold partitionOscillation
  let inc : Fin P.n → ℝ := fun i => α (P.pts i.succ) - α (P.pts i.castSucc)
  have htel :
      (∑ i : Fin P.n, inc i) = α b - α a := by
    simpa [inc, P.pts_start, P.pts_end] using sum_adjacent_sub_local (fun i => α (P.pts i))
  have hsum_le :
      (∑ i : Fin P.n,
        (upperStep P f i - lowerStep P f i) * inc i)
        ≤ ∑ i : Fin P.n,
            (eta * inc i + if i.val ∈ B then (2 * C) * inc i else 0) := by
    refine Finset.sum_le_sum ?_
    intro i hi_mem
    have hinc_nonneg : 0 ≤ inc i :=
      DarbouxRS.partition_increment_nonneg_of_source_core_local P
        ⟨hab, hAbove, hBelow, hmono⟩
    by_cases hiB : i.val ∈ B
    · have hterm :
          (upperStep P f i - lowerStep P f i) * inc i ≤
            (2 * C) * inc i :=
        mul_le_mul_of_nonneg_right (hbad i hiB) hinc_nonneg
      have heta_inc : 0 ≤ eta * inc i := mul_nonneg heta_nonneg hinc_nonneg
      simp [hiB]
      linarith
    · have hterm :
          (upperStep P f i - lowerStep P f i) * inc i ≤
            eta * inc i :=
        mul_le_mul_of_nonneg_right (hgood i hiB) hinc_nonneg
      simp [hiB]
      exact hterm
  have hsum_eq :
      (∑ i : Fin P.n,
            (eta * inc i + if i.val ∈ B then (2 * C) * inc i else 0)) =
        eta * (α b - α a) +
          2 * C *
            (∑ i ∈ (Finset.univ : Finset (Fin P.n)).filter (fun i => i.val ∈ B), inc i) := by
    rw [Finset.sum_add_distrib]
    have hfirst :
        (∑ i : Fin P.n, eta * inc i) = eta * (α b - α a) := by
      rw [← Finset.mul_sum, htel]
    have hsecond :
        (∑ i : Fin P.n, (if i.val ∈ B then (2 * C) * inc i else 0)) =
          2 * C *
            (∑ i ∈ (Finset.univ : Finset (Fin P.n)).filter (fun i => i.val ∈ B), inc i) := by
      calc
        (∑ i : Fin P.n, (if i.val ∈ B then (2 * C) * inc i else 0))
            = ∑ i ∈ (Finset.univ : Finset (Fin P.n)).filter (fun i => i.val ∈ B),
                (2 * C) * inc i := by
              rw [Finset.sum_filter]
        _ = 2 * C *
              (∑ i ∈ (Finset.univ : Finset (Fin P.n)).filter (fun i => i.val ∈ B), inc i) := by
              rw [Finset.mul_sum]
    rw [hfirst, hsecond]
  exact le_trans hsum_le (le_of_eq hsum_eq)

private lemma partition_increment_sum_Ico_le_bad_interval
    {α : ℝ → ℝ} {a b c r : ℝ}
    (hα_mono : Monotone α)
    (P : Partition a b) {j0 j1 : ℕ}
    (hj0j1 : j0 ≤ j1)
    (_hj1 : j1 ≤ P.n)
    (hleft : c - r ≤ pointAtNat P j0)
    (hright : pointAtNat P j1 ≤ c + r) :
    (∑ i ∈ Finset.Ico j0 j1,
        (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) ≤
      α (c + r) - α (c - r) := by
  have htel :
      (∑ i ∈ Finset.Ico j0 j1,
          (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) =
        α (pointAtNat P j1) - α (pointAtNat P j0) := by
    exact Finset.sum_Ico_sub (fun k => α (pointAtNat P k)) hj0j1
  have hα_left : α (c - r) ≤ α (pointAtNat P j0) := hα_mono hleft
  have hα_right : α (pointAtNat P j1) ≤ α (c + r) := hα_mono hright
  rw [htel]
  linarith

private lemma partition_increment_sum_Ico_blocks_le_bad_intervals
    {α : ℝ → ℝ} {a b : ℝ}
    (hα_mono : Monotone α)
    (P : Partition a b)
    (S : Finset ℝ) (rho : ℝ → ℝ) (lo hi : ℝ → ℕ)
    (hlohi : ∀ c : ℝ, c ∈ S → lo c ≤ hi c)
    (hhi : ∀ c : ℝ, c ∈ S → hi c ≤ P.n)
    (hleft : ∀ c : ℝ, c ∈ S → c - rho c ≤ pointAtNat P (lo c))
    (hright : ∀ c : ℝ, c ∈ S → pointAtNat P (hi c) ≤ c + rho c) :
    (∑ c ∈ S,
        ∑ i ∈ Finset.Ico (lo c) (hi c),
          (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) ≤
      ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) := by
  refine Finset.sum_le_sum ?_
  intro c hc
  exact partition_increment_sum_Ico_le_bad_interval hα_mono P
    (hlohi c hc) (hhi c hc) (hleft c hc) (hright c hc)

private lemma partition_increment_sum_le_bad_intervals_of_disjoint_Ico_cover
    {α : ℝ → ℝ} {a b : ℝ}
    (hα_mono : Monotone α)
    (P : Partition a b)
    (B : Finset ℕ) (S : Finset ℝ) (rho : ℝ → ℝ) (lo hi : ℝ → ℕ)
    (hdisj :
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Finset.Ico (lo c) (hi c)))
    (hcover :
      B ⊆ S.biUnion (fun c : ℝ => Finset.Ico (lo c) (hi c)))
    (hlohi : ∀ c : ℝ, c ∈ S → lo c ≤ hi c)
    (hhi : ∀ c : ℝ, c ∈ S → hi c ≤ P.n)
    (hleft : ∀ c : ℝ, c ∈ S → c - rho c ≤ pointAtNat P (lo c))
    (hright : ∀ c : ℝ, c ∈ S → pointAtNat P (hi c) ≤ c + rho c) :
    (∑ i ∈ B, (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) ≤
      ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) := by
  let blockUnion : Finset ℕ :=
    S.biUnion (fun c : ℝ => Finset.Ico (lo c) (hi c))
  let inc : ℕ → ℝ := fun i => α (pointAtNat P (i + 1)) - α (pointAtNat P i)
  have hB_le_union :
      (∑ i ∈ B, inc i) ≤ ∑ i ∈ blockUnion, inc i := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hcover ?_
    intro i hi_union _hi_not_B
    rcases (Finset.mem_biUnion.mp hi_union) with ⟨c, hcS, hiIco⟩
    have hi_lt : i < P.n := by
      have hi_block := (Finset.mem_Ico.mp hiIco).2
      exact lt_of_lt_of_le hi_block (hhi c hcS)
    have hpts : pointAtNat P i ≤ pointAtNat P (i + 1) :=
      pointAtNat_mono P (Nat.le_of_lt hi_lt) (Nat.succ_le_of_lt hi_lt) (by omega)
    have hα : α (pointAtNat P i) ≤ α (pointAtNat P (i + 1)) := hα_mono hpts
    dsimp [inc]
    linarith
  have hunion_eq :
      (∑ i ∈ blockUnion, inc i) =
        ∑ c ∈ S, ∑ i ∈ Finset.Ico (lo c) (hi c), inc i := by
    dsimp [blockUnion]
    exact Finset.sum_biUnion hdisj
  have hblocks_le :
      (∑ c ∈ S,
          ∑ i ∈ Finset.Ico (lo c) (hi c),
            (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) ≤
        ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) :=
    partition_increment_sum_Ico_blocks_le_bad_intervals hα_mono P S rho lo hi
      hlohi hhi hleft hright
  calc
    (∑ i ∈ B, (α (pointAtNat P (i + 1)) - α (pointAtNat P i)))
        = ∑ i ∈ B, inc i := by rfl
    _ ≤ ∑ i ∈ blockUnion, inc i := hB_le_union
    _ = ∑ c ∈ S, ∑ i ∈ Finset.Ico (lo c) (hi c), inc i := hunion_eq
    _ = ∑ c ∈ S,
          ∑ i ∈ Finset.Ico (lo c) (hi c),
            (α (pointAtNat P (i + 1)) - α (pointAtNat P i)) := by rfl
    _ ≤ ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) := hblocks_le

lemma badCellIndices_half_radius_subset_Ico_blocks_of_endpointBlock_cover
    {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ)
    (lo hi : ℝ → ℕ)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hmesh : ∀ c : ℝ, c ∈ S → P.mesh < rho c / 2)
    (hblock_cover :
      ∀ c : ℝ, c ∈ S →
        badPointEndpointBlock P c (rho c) ⊆ Finset.Ico (lo c) (hi c)) :
    badCellIndices P S (fun c : ℝ => rho c / 2) ⊆
      S.biUnion (fun c : ℝ => Finset.Ico (lo c) (hi c)) := by
  classical
  intro i hi_bad
  have hendpoint_cover :=
    badCellIndices_half_radius_subset_badPointEndpointBlocks_local
      P S rho hrho_pos hmesh hi_bad
  rcases (Finset.mem_biUnion.mp hendpoint_cover) with ⟨c, hcS, hi_block⟩
  exact Finset.mem_biUnion.mpr ⟨c, hcS, hblock_cover c hcS hi_block⟩

private lemma partition_increment_sum_badCellIndices_half_radius_le_bad_intervals
    {α : ℝ → ℝ} {a b : ℝ}
    (hα_mono : Monotone α)
    (P : Partition a b)
    (S : Finset ℝ) (rho : ℝ → ℝ) (lo hi : ℝ → ℕ)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hmesh : ∀ c : ℝ, c ∈ S → P.mesh < rho c / 2)
    (hblock_cover :
      ∀ c : ℝ, c ∈ S →
        badPointEndpointBlock P c (rho c) ⊆ Finset.Ico (lo c) (hi c))
    (hdisj :
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Finset.Ico (lo c) (hi c)))
    (hlohi : ∀ c : ℝ, c ∈ S → lo c ≤ hi c)
    (hhi : ∀ c : ℝ, c ∈ S → hi c ≤ P.n)
    (hleft : ∀ c : ℝ, c ∈ S → c - rho c ≤ pointAtNat P (lo c))
    (hright : ∀ c : ℝ, c ∈ S → pointAtNat P (hi c) ≤ c + rho c) :
    (∑ i ∈ badCellIndices P S (fun c : ℝ => rho c / 2),
        (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) ≤
      ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) := by
  classical
  refine partition_increment_sum_le_bad_intervals_of_disjoint_Ico_cover
    hα_mono P (badCellIndices P S (fun c : ℝ => rho c / 2))
    S rho lo hi hdisj ?_ hlohi hhi hleft hright
  exact badCellIndices_half_radius_subset_Ico_blocks_of_endpointBlock_cover
    P S rho lo hi hrho_pos hmesh hblock_cover

private lemma partition_increment_sum_badCellIndices_half_radius_le_bad_intervals_canonical
    {α : ℝ → ℝ} {a b : ℝ}
    (hα_mono : Monotone α)
    (P : Partition a b)
    (S : Finset ℝ) (rho : ℝ → ℝ)
    (hcI : ∀ c : ℝ, c ∈ S → c ∈ Icc a b)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hmesh : ∀ c : ℝ, c ∈ S → P.mesh < rho c / 2)
    (hsep :
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c))) :
    (∑ i ∈ badCellIndices P S (fun c : ℝ => rho c / 2),
        (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) ≤
      ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) := by
  refine partition_increment_sum_badCellIndices_half_radius_le_bad_intervals
    hα_mono P S rho
    (fun c : ℝ => badPointCanonicalLo P c (rho c))
    (fun c : ℝ => badPointCanonicalHi P c (rho c))
    hrho_pos hmesh ?_ ?_ ?_ ?_ ?_ ?_
  · intro c hc
    exact badPointEndpointBlock_subset_canonical_Ico_local P (hcI c hc) (hrho_pos c hc)
  · exact badPointCanonicalIcoBlocks_pairwiseDisjoint_of_pairwiseDisjoint_Ioo_local
      P S rho hcI hrho_pos hsep
  · intro c hc
    exact badPointCanonicalLo_le_hi_of_mesh P (hcI c hc) (hrho_pos c hc) (hmesh c hc)
  · intro c hc
    exact badPointCanonicalHi_le_n P (hcI c hc) (hrho_pos c hc)
  · intro c hc
    exact badPointCanonicalLo_left_bound P (hcI c hc) (hrho_pos c hc)
  · intro c hc
    exact badPointCanonicalHi_right_bound P (hcI c hc) (hrho_pos c hc)

private lemma partitionOscillation_le_goodRemainder_badCell_split
    {f α : ℝ → ℝ} {a b C eta δgood : ℝ}
    {S : Finset ℝ} {rho : ℝ → ℝ}
    (hs : SourceHypotheses a b f α)
    (P : Partition a b)
    (hC : ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C)
    (heta_nonneg : 0 ≤ eta)
    (hgood_step :
      ∀ (P' : Partition a b) (i : Fin P'.n),
        P'.mesh < δgood →
        Partition.subinterval P' i ⊆ goodRemainder a b S rho →
          upperStep P' f i - lowerStep P' f i < eta)
    (hmesh_good : P.mesh < δgood) :
    partitionOscillation P f α ≤
      eta * (α b - α a) +
        2 * C *
          (∑ i ∈ badCellIndices P S rho,
            (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) := by
  rcases hs with ⟨hab, hAbove, hBelow, hmono⟩
  let hs' : SourceHypotheses a b f α :=
    ⟨hab, hAbove, hBelow, hmono⟩
  have hsplit := partitionOscillation_le_good_bad_split_local
    (f := f) (α := α) (a := a) (b := b) (C := C) (eta := eta)
    hs' P (badCellIndices P S rho) heta_nonneg
    (fun i hi_not_bad =>
      le_of_lt (hgood_step P i hmesh_good
        (cell_subset_goodRemainder_of_not_mem_badCellIndices_local P S rho i hi_not_bad)))
    (fun i _hi_bad =>
      upperStep_sub_lowerStep_le_two_mul_abs_bound_local P i hAbove hBelow hC)
  have hfin_to_range :
      (∑ i ∈ (Finset.univ : Finset (Fin P.n)).filter
          (fun i => i.val ∈ badCellIndices P S rho),
          (α (P.pts i.succ) - α (P.pts i.castSucc))) =
        ∑ i ∈ (Finset.range P.n).filter (fun i => i ∈ badCellIndices P S rho),
          (α (pointAtNat P (i + 1)) - α (pointAtNat P i)) := by
    rw [Finset.sum_filter]
    calc
      (∑ i : Fin P.n,
          if i.val ∈ badCellIndices P S rho then
            α (P.pts i.succ) - α (P.pts i.castSucc)
          else 0) =
          ∑ i : Fin P.n,
            if i.val ∈ badCellIndices P S rho then
              α (pointAtNat P (i.val + 1)) - α (pointAtNat P i.val)
            else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i _
              by_cases hi : i.val ∈ badCellIndices P S rho
              · simp only [hi, if_true]
                rw [pointAtNat_eq P (Nat.succ_le_of_lt i.isLt),
                  pointAtNat_eq P (Nat.le_of_lt i.isLt)]
                rfl
              · simp [hi]
      _ = ∑ i ∈ Finset.range P.n,
            if i ∈ badCellIndices P S rho then
              α (pointAtNat P (i + 1)) - α (pointAtNat P i)
            else 0 := by
              exact Fin.sum_univ_eq_sum_range (fun i : ℕ =>
                if i ∈ badCellIndices P S rho then
                  α (pointAtNat P (i + 1)) - α (pointAtNat P i)
                else 0) P.n
      _ = ∑ i ∈ (Finset.range P.n).filter (fun i => i ∈ badCellIndices P S rho),
            (α (pointAtNat P (i + 1)) - α (pointAtNat P i)) := by
              rw [Finset.sum_filter]
  have hfilter_eq :
      (Finset.range P.n).filter (fun i => i ∈ badCellIndices P S rho) =
        badCellIndices P S rho := by
    ext i
    constructor
    · intro hi
      exact (Finset.mem_filter.mp hi).2
    · intro hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr ((mem_badCellIndices_iff_local P S rho).mp hi).1, hi⟩
  rw [hfin_to_range, hfilter_eq] at hsplit
  exact hsplit

theorem sol_core_badIntervals
    {f α : ℝ → ℝ} {a b C eta δgood : ℝ}
    {S : Finset ℝ} {rho : ℝ → ℝ}
    (hs : SourceHypotheses a b f α)
    (hα_mono : Monotone α)
    (P : Partition a b)
    (hC : ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C)
    (hC_nonneg : 0 ≤ C)
    (heta_nonneg : 0 ≤ eta)
    (hgood_step :
      ∀ (P' : Partition a b) (i : Fin P'.n),
        P'.mesh < δgood →
        Partition.subinterval P' i ⊆
          goodRemainder a b S (fun c : ℝ => rho c / 2) →
          upperStep P' f i - lowerStep P' f i < eta)
    (hmesh_good : P.mesh < δgood)
    (hcI : ∀ c : ℝ, c ∈ S → c ∈ Icc a b)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hmesh_bad : ∀ c : ℝ, c ∈ S → P.mesh < rho c / 2)
    (hsep :
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c))) :
    partitionOscillation P f α ≤
      eta * (α b - α a) +
        2 * C * ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) := by
  have h1 := partitionOscillation_le_goodRemainder_badCell_split (rho := fun c => rho c / 2)
    hs P hC heta_nonneg hgood_step hmesh_good
  have h2 := partition_increment_sum_badCellIndices_half_radius_le_bad_intervals_canonical
    hα_mono P S rho hcI hrho_pos hmesh_bad hsep
  have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ 2 * C)
  linarith

end Thm11SourceRoute

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

theorem sol_exists_goodRemainder_uniform_oscillation
    {f : ℝ → ℝ} {a b eta : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ}
    (hS : ∀ x : ℝ, x ∈ S ↔ x ∈ discontinuitySetOn f a b)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ x : ℝ, x ∈ goodRemainder a b S rho →
      ∀ y : ℝ, y ∈ goodRemainder a b S rho →
        |x - y| < delta → |f x - f y| < eta := by
  have huc := (sol_isCompact_goodRemainder (a := a) (b := b) (S := S) (rho := rho)).uniformContinuousOn_of_continuous
    (sol_continuousOn_goodRemainder hS hrho_pos)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, h⟩ := huc eta heta
  refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
  have := h x hx y hy (by rw [Real.dist_eq]; exact hxy)
  rwa [Real.dist_eq] at this

theorem t16_sep (S : Finset ℝ) : ∃ d : ℝ, 0 < d ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → d ≤ |x - y| := by
  classical
  set D := (S.offDiag).image (fun p : ℝ × ℝ => |p.1 - p.2|) with hD
  by_cases h : D.Nonempty
  · refine ⟨D.min' h, ?_, ?_⟩
    · obtain ⟨p, hp, hpe⟩ := Finset.mem_image.1 (D.min'_mem h)
      rw [Finset.mem_offDiag] at hp
      rw [← hpe]
      exact abs_pos.2 (sub_ne_zero.2 hp.2.2)
    · intro x hx y hy hxy
      exact D.min'_le _ (Finset.mem_image.2 ⟨(x, y), Finset.mem_offDiag.2 ⟨hx, hy, hxy⟩, rfl⟩)
  · refine ⟨1, one_pos, fun x hx y hy hxy => ?_⟩
    exact absurd ⟨_, Finset.mem_image.2 ⟨(x, y), Finset.mem_offDiag.2 ⟨hx, hy, hxy⟩, rfl⟩⟩ h

theorem sol_finite_discontinuity_alpha_local_increment_pairwise_data
    {f α : ℝ → ℝ} {a b eps : ℝ}
    (hα_mono : Monotone α)
    (hDiscFinite : (discontinuitySetOn f a b).Finite)
    (hαCont :
      ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x)
    (heps : 0 < eps) :
    ∃ S : Finset ℝ,
      (∀ x : ℝ, x ∈ S ↔ x ∈ discontinuitySetOn f a b) ∧
      ∃ rho : ℝ → ℝ,
        (∀ c : ℝ, c ∈ S → 0 < rho c) ∧
        (∑ c ∈ S, (α (c + rho c) - α (c - rho c))) < eps ∧
        (↑S : Set ℝ).PairwiseDisjoint
          (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c)) := by
  obtain ⟨S, hS, rho0, hpos0, hsum0⟩ :=
    sol_finite_discontinuity_alpha_local_increment_data hDiscFinite hαCont heps
  obtain ⟨d, hd, hsep⟩ := t16_sep S
  refine ⟨S, hS, fun c => min (rho0 c) (d / 2), fun c hc => lt_min (hpos0 c hc) (by linarith), ?_, ?_⟩
  · refine lt_of_le_of_lt (Finset.sum_le_sum fun c hc => ?_) hsum0
    have h1 := hα_mono (show c + min (rho0 c) (d / 2) ≤ c + rho0 c by linarith [min_le_left (rho0 c) (d / 2)])
    have h2 := hα_mono (show c - rho0 c ≤ c - min (rho0 c) (d / 2) by linarith [min_le_left (rho0 c) (d / 2)])
    linarith
  · intro c hc e he hce
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    rintro z ⟨z1, z2⟩ ⟨z3, z4⟩
    have hm1 := min_le_right (rho0 c) (d / 2)
    have hm2 := min_le_right (rho0 e) (d / 2)
    have := hsep c hc e he hce
    rw [le_abs] at this
    rcases this with h | h <;> linarith

lemma t17_mem_node {a b : ℝ} (l : List ℝ)
    (hlen : 2 ≤ l.length)
    (hstart : l.getD 0 b = a)
    (hend : l.getD (l.length - 1) a = b)
    (hstrict : ∀ {i : ℕ}, i + 1 < l.length → l.getD i b < l.getD (i + 1) b)
    {x : ℝ} (hx : x ∈ l) :
    ∃ j : Fin ((partitionOfStrictEndpointList l hlen hstart hend hstrict).n + 1),
      (partitionOfStrictEndpointList l hlen hstart hend hstrict).pts j = x := by
  rcases List.mem_iff_getElem.1 hx with ⟨j, hj, hjx⟩
  have hjFin : j < (partitionOfStrictEndpointList l hlen hstart hend hstrict).n + 1 := by
    simp [partitionOfStrictEndpointList]
    omega
  refine ⟨⟨j, hjFin⟩, ?_⟩
  change l.getD j b = x
  rw [List.getD_eq_getElem l b hj]
  exact hjx

lemma t17_adj {a b δ : ℝ}
    (P Q : Partition a b)
    (hPmesh : P.mesh < δ) (hQmesh : Q.mesh < δ)
    {i : ℕ}
    (hi : i + 1 < (commonRefinementPointList P Q).length) :
    (commonRefinementPointList P Q).getD (i + 1) b -
        (commonRefinementPointList P Q).getD i b < δ := by
  let l := commonRefinementPointList P Q
  have hi0 : i < l.length := Nat.lt_trans (Nat.lt_succ_self i) hi
  have hleft_mem : l.getD i b ∈ l :=
    list_getD_mem_of_lt (l := l) (fallback := b) hi0
  rcases (mem_commonRefinementPointList_iff P Q).1 hleft_mem with hP | hQ
  · rcases (mem_partitionPointSet_iff P).1 hP with ⟨k, hkleft⟩
    have hle :=
      commonRefinementPointList_adjacent_length_le_mesh_of_left_partition
        P Q k hi hkleft.symm
    exact lt_of_le_of_lt hle hPmesh
  · rcases (mem_partitionPointSet_iff Q).1 hQ with ⟨k, hkleft⟩
    have hle :=
      commonRefinementPointList_adjacent_length_le_mesh_of_right_partition
        P Q k hi hkleft.symm
    exact lt_of_le_of_lt hle hQmesh



def t17pan {a b : ℝ} (P : Partition a b) (j : ℕ) : ℝ :=
  if h : j ≤ P.n then P.pts ⟨j, Nat.lt_succ_iff.mpr h⟩ else b
lemma t17pan_eq {a b : ℝ} (P : Partition a b)
    {j : ℕ} (hj : j ≤ P.n) :
    t17pan P j = P.pts ⟨j, Nat.lt_succ_iff.mpr hj⟩ := by
  simp [t17pan, hj]
def t17lowerTerm {a b : ℝ} (P : Partition a b)
    (f α : ℝ → ℝ) (i : ℕ) : ℝ :=
  if h : i < P.n then
    let iFin : Fin P.n := ⟨i, h⟩
    lowerStep P f iFin *
      (α (P.pts iFin.succ) - α (P.pts iFin.castSucc))
  else 0
def t17upperTerm {a b : ℝ} (P : Partition a b)
    (f α : ℝ → ℝ) (i : ℕ) : ℝ :=
  if h : i < P.n then
    let iFin : Fin P.n := ⟨i, h⟩
    upperStep P f iFin *
      (α (P.pts iFin.succ) - α (P.pts iFin.castSucc))
  else 0
lemma t17lowerTerm_eq {a b : ℝ} (P : Partition a b)
    (f α : ℝ → ℝ) {i : ℕ} (hi : i < P.n) :
    t17lowerTerm P f α i =
      lowerStep P f (⟨i, hi⟩ : Fin P.n) *
        (α (P.pts (⟨i, hi⟩ : Fin P.n).succ) -
          α (P.pts (⟨i, hi⟩ : Fin P.n).castSucc)) := by
  simp [t17lowerTerm, hi]
lemma t17upperTerm_eq {a b : ℝ} (P : Partition a b)
    (f α : ℝ → ℝ) {i : ℕ} (hi : i < P.n) :
    t17upperTerm P f α i =
      upperStep P f (⟨i, hi⟩ : Fin P.n) *
        (α (P.pts (⟨i, hi⟩ : Fin P.n).succ) -
          α (P.pts (⟨i, hi⟩ : Fin P.n).castSucc)) := by
  simp [t17upperTerm, hi]
lemma lowerSum_eq_sum_t17lowerTerm_range {a b : ℝ}
    (P : Partition a b) (f α : ℝ → ℝ) :
    lowerSum P f α =
      ∑ i ∈ Finset.range P.n, t17lowerTerm P f α i := by
  unfold lowerSum
  calc
    (∑ i : Fin P.n,
        lowerStep P f i *
          (α (P.pts i.succ) - α (P.pts i.castSucc))) =
        ∑ i : Fin P.n, t17lowerTerm P f α i.val := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [t17lowerTerm_eq P f α i.isLt]
    _ = ∑ i ∈ Finset.range P.n, t17lowerTerm P f α i :=
      Fin.sum_univ_eq_sum_range (t17lowerTerm P f α) P.n
lemma upperSum_eq_sum_t17upperTerm_range {a b : ℝ}
    (P : Partition a b) (f α : ℝ → ℝ) :
    upperSum P f α =
      ∑ i ∈ Finset.range P.n, t17upperTerm P f α i := by
  unfold upperSum
  calc
    (∑ i : Fin P.n,
        upperStep P f i *
          (α (P.pts i.succ) - α (P.pts i.castSucc))) =
        ∑ i : Fin P.n, t17upperTerm P f α i.val := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [t17upperTerm_eq P f α i.isLt]
    _ = ∑ i ∈ Finset.range P.n, t17upperTerm P f α i :=
      Fin.sum_univ_eq_sum_range (t17upperTerm P f α) P.n

lemma t17_lower_cell_le_block_sum
    {f α : ℝ → ℝ} {a b : ℝ}
    (hs : SourceHypotheses a b f α)
    {R P : Partition a b} (href : DarbouxPartitionRefines R P)
    (i : Fin P.n) :
    lowerStep P f i *
        (α (P.pts i.succ) - α (P.pts i.castSucc)) ≤
      ∑ k ∈ Finset.Ico
          (href.index i.castSucc).val
          (href.index i.succ).val,
        t17lowerTerm R f α k := by
  rcases hs with ⟨hab, hAbove, hBelow, hmonoα⟩
  let j0 := (href.index i.castSucc).val
  let j1 := (href.index i.succ).val
  have hj0j1 : j0 ≤ j1 := le_of_lt
    (DarbouxPartitionRefines.index_strictMono href Fin.castSucc_lt_succ)
  have hj1_le : j1 ≤ R.n := DarbouxPartitionRefines.index_le href i.succ
  have htel :
      (∑ k ∈ Finset.Ico j0 j1,
          (α (t17pan R (k + 1)) - α (t17pan R k))) =
        α (t17pan R j1) - α (t17pan R j0) := by
    exact Finset.sum_Ico_sub (fun k => α (t17pan R k)) hj0j1
  calc
    lowerStep P f i *
        (α (P.pts i.succ) - α (P.pts i.castSucc))
        = lowerStep P f i *
          (α (t17pan R j1) - α (t17pan R j0)) := by
            rw [t17pan_eq R hj1_le,
              t17pan_eq R (DarbouxPartitionRefines.index_le href i.castSucc)]
            rw [DarbouxPartitionRefines.index_pts href i.succ,
              DarbouxPartitionRefines.index_pts href i.castSucc]
    _ = lowerStep P f i *
          (∑ k ∈ Finset.Ico j0 j1,
            (α (t17pan R (k + 1)) - α (t17pan R k))) := by rw [htel]
    _ = ∑ k ∈ Finset.Ico j0 j1,
          lowerStep P f i *
            (α (t17pan R (k + 1)) - α (t17pan R k)) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.Ico j0 j1,
          t17lowerTerm R f α k := by
        refine Finset.sum_le_sum ?_
        intro k hk_mem
        have hkI := Finset.mem_Ico.mp hk_mem
        have hk_lt_j1 : k < j1 := hkI.2
        have hk_left : j0 ≤ k := hkI.1
        have hk_right : k + 1 ≤ j1 := Nat.succ_le_of_lt hk_lt_j1
        have hk_lt_Rn : k < R.n := lt_of_lt_of_le hk_lt_j1 hj1_le
        let kFin : Fin R.n := ⟨k, hk_lt_Rn⟩
        have hsub :
            Partition.subinterval R kFin ⊆ Partition.subinterval P i := by
          apply DarbouxPartitionRefines.subinterval_subset_of_index_block href
          · exact_mod_cast hk_left
          · exact_mod_cast hk_right
        have hstep :
            lowerStep P f i ≤ lowerStep R f kFin :=
          lowerStep_le_lowerStep_of_subinterval_subset P R hBelow hsub
        have hinc :
            0 ≤ α (R.pts kFin.succ) - α (R.pts kFin.castSucc) :=
          t11_incr_nonneg ⟨hab, hAbove, hBelow, hmonoα⟩ R kFin
        rw [t17lowerTerm_eq R f α hk_lt_Rn,
          t17pan_eq R (Nat.succ_le_of_lt hk_lt_Rn),
          t17pan_eq R (Nat.le_of_lt hk_lt_Rn)]
        exact mul_le_mul_of_nonneg_right hstep hinc
lemma t17_upper_block_sum_le_cell
    {f α : ℝ → ℝ} {a b : ℝ}
    (hs : SourceHypotheses a b f α)
    {R P : Partition a b} (href : DarbouxPartitionRefines R P)
    (i : Fin P.n) :
      (∑ k ∈ Finset.Ico
          (href.index i.castSucc).val
          (href.index i.succ).val,
        t17upperTerm R f α k) ≤
      upperStep P f i *
        (α (P.pts i.succ) - α (P.pts i.castSucc)) := by
  rcases hs with ⟨hab, hAbove, hBelow, hmonoα⟩
  let j0 := (href.index i.castSucc).val
  let j1 := (href.index i.succ).val
  have hj0j1 : j0 ≤ j1 := le_of_lt
    (DarbouxPartitionRefines.index_strictMono href Fin.castSucc_lt_succ)
  have hj1_le : j1 ≤ R.n := DarbouxPartitionRefines.index_le href i.succ
  have htel :
      (∑ k ∈ Finset.Ico j0 j1,
          (α (t17pan R (k + 1)) - α (t17pan R k))) =
        α (t17pan R j1) - α (t17pan R j0) := by
    exact Finset.sum_Ico_sub (fun k => α (t17pan R k)) hj0j1
  calc
    (∑ k ∈ Finset.Ico j0 j1,
        t17upperTerm R f α k)
        ≤ ∑ k ∈ Finset.Ico j0 j1,
          upperStep P f i *
            (α (t17pan R (k + 1)) - α (t17pan R k)) := by
          refine Finset.sum_le_sum ?_
          intro k hk_mem
          have hkI := Finset.mem_Ico.mp hk_mem
          have hk_lt_j1 : k < j1 := hkI.2
          have hk_left : j0 ≤ k := hkI.1
          have hk_right : k + 1 ≤ j1 := Nat.succ_le_of_lt hk_lt_j1
          have hk_lt_Rn : k < R.n := lt_of_lt_of_le hk_lt_j1 hj1_le
          let kFin : Fin R.n := ⟨k, hk_lt_Rn⟩
          have hsub :
              Partition.subinterval R kFin ⊆ Partition.subinterval P i := by
            apply DarbouxPartitionRefines.subinterval_subset_of_index_block href
            · exact_mod_cast hk_left
            · exact_mod_cast hk_right
          have hstep :
              upperStep R f kFin ≤ upperStep P f i :=
            upperStep_le_upperStep_of_subinterval_subset P R hAbove hsub
          have hinc :
              0 ≤ α (R.pts kFin.succ) - α (R.pts kFin.castSucc) :=
            t11_incr_nonneg ⟨hab, hAbove, hBelow, hmonoα⟩ R kFin
          rw [t17upperTerm_eq R f α hk_lt_Rn,
            t17pan_eq R (Nat.succ_le_of_lt hk_lt_Rn),
            t17pan_eq R (Nat.le_of_lt hk_lt_Rn)]
          exact mul_le_mul_of_nonneg_right hstep hinc
    _ = upperStep P f i *
          (∑ k ∈ Finset.Ico j0 j1,
            (α (t17pan R (k + 1)) - α (t17pan R k))) := by
        rw [Finset.mul_sum]
    _ = upperStep P f i *
          (α (t17pan R j1) - α (t17pan R j0)) := by rw [htel]
    _ = upperStep P f i *
        (α (P.pts i.succ) - α (P.pts i.castSucc)) := by
          rw [t17pan_eq R hj1_le,
            t17pan_eq R (DarbouxPartitionRefines.index_le href i.castSucc)]
          rw [DarbouxPartitionRefines.index_pts href i.succ,
            DarbouxPartitionRefines.index_pts href i.castSucc]

theorem sol_partitionOfStrictEndpointList_mem_node {a b : ℝ} (l : List ℝ)
    (hlen : 2 ≤ l.length)
    (hstart : l.getD 0 b = a)
    (hend : l.getD (l.length - 1) a = b)
    (hstrict : ∀ {i : ℕ}, i + 1 < l.length → l.getD i b < l.getD (i + 1) b)
    {x : ℝ} (hx : x ∈ l) :
    ∃ j : Fin ((partitionOfStrictEndpointList l hlen hstart hend hstrict).n + 1),
      (partitionOfStrictEndpointList l hlen hstart hend hstrict).pts j = x :=
  t17_mem_node l hlen hstart hend hstrict hx

theorem sol_commonRefinementPointList_adjacent_length_lt_delta {a b δ : ℝ}
    (P Q : Partition a b)
    (hPmesh : P.mesh < δ) (hQmesh : Q.mesh < δ)
    {i : ℕ}
    (hi : i + 1 < (commonRefinementPointList P Q).length) :
    (commonRefinementPointList P Q).getD (i + 1) b -
        (commonRefinementPointList P Q).getD i b < δ :=
  t17_adj P Q hPmesh hQmesh hi

theorem t17_blocks {a b : ℝ} {R P : Partition a b} (href : DarbouxPartitionRefines R P) (g : ℕ → ℝ) :
    (∑ i : Fin P.n, ∑ k ∈ Finset.Ico (href.index i.castSucc).val (href.index i.succ).val, g k) =
      ∑ k ∈ Finset.range R.n, g k := by
  rw [← sum_Ico_refinement_blocks_eq_range href g]
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ k ∈ Finset.Ico (href.indexD i) (href.indexD (i + 1)), g k) P.n]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [DarbouxPartitionRefines.indexD_eq_index href (Nat.le_of_lt i.isLt),
    DarbouxPartitionRefines.indexD_eq_index href (Nat.succ_le_of_lt i.isLt)]
  rfl

theorem sol_DarbouxRefinementSumMonotone_proof
    {f α : ℝ → ℝ} {a b : ℝ} :
    DarbouxRefinementSumMonotone a b f α := by
  intro hs P R href
  constructor
  · calc lowerSum P f α
        = ∑ i : Fin P.n, lowerStep P f i * (α (P.pts i.succ) - α (P.pts i.castSucc)) := rfl
      _ ≤ ∑ i : Fin P.n, ∑ k ∈ Finset.Ico (href.index i.castSucc).val (href.index i.succ).val,
            t17lowerTerm R f α k :=
          Finset.sum_le_sum fun i _ => t17_lower_cell_le_block_sum hs href i
      _ = ∑ k ∈ Finset.range R.n, t17lowerTerm R f α k := t17_blocks href _
      _ = lowerSum R f α := (lowerSum_eq_sum_t17lowerTerm_range R f α).symm
  · calc upperSum R f α
        = ∑ k ∈ Finset.range R.n, t17upperTerm R f α k := upperSum_eq_sum_t17upperTerm_range R f α
      _ = ∑ i : Fin P.n, ∑ k ∈ Finset.Ico (href.index i.castSucc).val (href.index i.succ).val,
            t17upperTerm R f α k := (t17_blocks href _).symm
      _ ≤ ∑ i : Fin P.n, upperStep P f i * (α (P.pts i.succ) - α (P.pts i.castSucc)) :=
          Finset.sum_le_sum fun i _ => t17_upper_block_sum_le_cell hs href i
      _ = upperSum P f α := rfl

theorem sol_DarbouxCommonRefinementSandwich_proof
    {f α : ℝ → ℝ} {a b : ℝ}
    (hs : SourceHypotheses a b f α) :
    DarbouxCommonRefinementSandwich a b f α :=
  sol_DarbouxCommonRefinementSandwich_of_exists_and_sumMonotone
    DarbouxCommonRefinementExists_concrete sol_DarbouxRefinementSumMonotone_proof hs

theorem sol_closedIntervalDarbouxFineCauchyFromGap_proof :
    ClosedIntervalDarbouxFineCauchyFromGap :=
  sol_closedIntervalDarbouxFineCauchyFromGap_of_commonRefinementSandwich
    (fun hs => sol_DarbouxCommonRefinementSandwich_proof hs)


theorem sol_partitionOscillation_le_goodRemainder_badIntervals
    {f α : ℝ → ℝ} {a b C eta δgood : ℝ}
    {S : Finset ℝ} {rho : ℝ → ℝ}
    (hs : SourceHypotheses a b f α)
    (hα_mono : Monotone α)
    (P : Partition a b)
    (hC : ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C)
    (hC_nonneg : 0 ≤ C)
    (heta_nonneg : 0 ≤ eta)
    (hgood_step :
      ∀ (P' : Partition a b) (i : Fin P'.n),
        P'.mesh < δgood →
        Partition.subinterval P' i ⊆
          goodRemainder a b S (fun c : ℝ => rho c / 2) →
          upperStep P' f i - lowerStep P' f i < eta)
    (hmesh_good : P.mesh < δgood)
    (hcI : ∀ c : ℝ, c ∈ S → c ∈ Icc a b)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hmesh_bad : ∀ c : ℝ, c ∈ S → P.mesh < rho c / 2)
    (hsep :
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c))) :
    partitionOscillation P f α ≤
      eta * (α b - α a) +
        2 * C * ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) :=
  Thm11SourceRoute.sol_core_badIntervals hs hα_mono P hC hC_nonneg heta_nonneg hgood_step hmesh_good
    hcI hrho_pos hmesh_bad hsep

theorem t18_min_pos (S : Finset ℝ) (g : ℝ → ℝ) (h : ∀ c ∈ S, 0 < g c) :
    ∃ d > 0, ∀ c ∈ S, d ≤ g c := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _; exact ⟨1, one_pos, by simp⟩
  · intro x s _ ih h
    obtain ⟨d, hd, hd'⟩ := ih (fun c hc => h c (Finset.mem_insert_of_mem hc))
    refine ⟨min d (g x), lt_min hd (h x (Finset.mem_insert_self _ _)), ?_⟩
    intro c hc
    rcases Finset.mem_insert.1 hc with rfl | hc
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hd' c hc)

theorem sol_strictFiniteDiscontinuityOscillationCriterion_proof :
    StrictFiniteDiscontinuityOscillationCriterion := by
  intro f α a b hab hmono hA hB hD hαC eps heps
  have hs : SourceHypotheses a b f α := ⟨hab, hA, hB, hmono.monotoneOn _⟩
  obtain ⟨M, hM⟩ := id hA
  obtain ⟨m, hm⟩ := id hB
  set C := max |M| |m| with hCdef
  have hC0 : 0 ≤ C := le_max_of_le_left (abs_nonneg _)
  have hC : ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C := by
    intro x hx
    have h1 : f x ≤ M := hM (Set.mem_image_of_mem f hx)
    have h2 : m ≤ f x := hm (Set.mem_image_of_mem f hx)
    have h3 : M ≤ C := (le_abs_self M).trans (le_max_left _ _)
    have h4 : -C ≤ m := by
      have := neg_abs_le m
      have : |m| ≤ C := le_max_right _ _
      linarith
    rw [abs_le]; constructor <;> linarith
  have hD0 : 0 ≤ α b - α a := sub_nonneg.2 (hmono hab.le)
  set eta := eps / (2 * (α b - α a + 1)) with heta_def
  have heta : 0 < eta := by positivity
  set eps' := eps / (2 * (2 * C + 1)) with heps'_def
  have heps' : 0 < eps' := by positivity
  obtain ⟨S, hS, rho, hrho, hsum, hsep⟩ :=
    sol_finite_discontinuity_alpha_local_increment_pairwise_data hmono hD hαC heps'
  obtain ⟨δg, hδg, hgood⟩ := sol_exists_upperStep_sub_lowerStep_lt_of_goodRemainder_cell
    (rho := fun c => rho c / 2) hS (fun c hc => by have := hrho c hc; positivity) hA hB heta
  obtain ⟨δb, hδb, hδb'⟩ := t18_min_pos S (fun c => rho c / 2) (fun c hc => by have := hrho c hc; positivity)
  refine ⟨min δg δb, lt_min hδg hδb, fun P hP => ?_⟩
  have hPg : P.mesh < δg := lt_of_lt_of_le hP (min_le_left _ _)
  have hPb : ∀ c ∈ S, P.mesh < rho c / 2 := fun c hc =>
    lt_of_lt_of_le (lt_of_lt_of_le hP (min_le_right _ _)) (hδb' c hc)
  have hcI : ∀ c : ℝ, c ∈ S → c ∈ Icc a b := fun c hc => ((hS c).1 hc).1
  have hmain := sol_partitionOscillation_le_goodRemainder_badIntervals hs hmono P hC hC0 heta.le
    (fun P' i h1 h2 => hgood P' i h1 h2) hPg hcI hrho hPb hsep
  have hA1 : eta * (α b - α a) < eps / 2 := by
    rw [heta_def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hA2 : 2 * C * ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) ≤ 2 * C * eps' :=
    mul_le_mul_of_nonneg_left hsum.le (by linarith)
  have hA3 : 2 * C * eps' < eps / 2 := by
    rw [heps'_def, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

theorem sol_strictFiniteDiscontinuityUpperLowerCriterion_proof :
    StrictFiniteDiscontinuityUpperLowerCriterion :=
  sol_strict_upperLower_criterion_of_oscillation
    (sol_closedIntervalDarbouxCommonLimitFromOscillation_of_gap
      (sol_closedIntervalDarbouxCommonLimitFromGap_of_fineCauchy
        sol_closedIntervalDarbouxFineCauchyFromGap_proof))
    sol_strictFiniteDiscontinuityOscillationCriterion_proof

theorem sol_strictFiniteDiscontinuityCommonLimitCriterion_proof :
    StrictFiniteDiscontinuityCommonLimitCriterion :=
  sol_strict_common_limit_criterion_of_upperLower_criterion
    sol_strictFiniteDiscontinuityUpperLowerCriterion_proof

theorem sol_strict_thm_1_1
    {f α : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hα_mono : Monotone α)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hDiscFinite : (discontinuitySetOn f a b).Finite)
    (hαCont : ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) :
    RSIntegrable f α a b :=
  sol_strict_thm_1_1_of_common_limit_criterion
    sol_strictFiniteDiscontinuityCommonLimitCriterion_proof hab hα_mono hAbove hBelow hDiscFinite hαCont

theorem solution
    {f α : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hα_mono : Monotone α)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hDiscFinite : (discontinuitySetOn f a b).Finite)
    (hαCont : ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) :
    RSIntegrable f α a b := by
  apply sol_strict_thm_1_1 <;> assumption
