-- Prove2me | solution 1 for Thm_1_4.taggedSum_derivative_identity_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:19:05.802224+00:00
-- url     : https://prove2.me/submissions/dad56f65-1936-43ae-ac60-160967c4bde4

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_4_F002
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
import Theorems.Thm_Thm_1_4_partition_length_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory DarbouxRS Thm_1_4
open scoped BigOperators Pointwise Interval
noncomputable section

private theorem source_taggedSum_derivative_identity_abs_le {f α α' : ℝ → ℝ} {a b C eta delta : ℝ}
    (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (hα'osc :
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
        |x - y| < delta → |α' x - α' y| ≤ eta)
    (hmesh : P.mesh < delta)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc a b → |f x| ≤ C)
    (hC : 0 ≤ C) :
    |taggedSum P tags f α -
        taggedSum P tags (fun x => f x * α' x) (fun x => x)| ≤
      C * eta * (b - a) := by
  have hsum_rewrite :
      taggedSum P tags f α -
          taggedSum P tags (fun x => f x * α' x) (fun x => x) =
        ∑ i : Fin P.n,
          (f (tags i) * (α (P.pts i.succ) - α (P.pts i.castSucc)) -
            (f (tags i) * α' (tags i)) *
              (P.pts i.succ - P.pts i.castSucc)) := by
    unfold taggedSum
    rw [← Finset.sum_sub_distrib]
  calc
    |taggedSum P tags f α -
        taggedSum P tags (fun x => f x * α' x) (fun x => x)|
        =
      |∑ i : Fin P.n,
          (f (tags i) * (α (P.pts i.succ) - α (P.pts i.castSucc)) -
            (f (tags i) * α' (tags i)) *
              (P.pts i.succ - P.pts i.castSucc))| := by
        rw [hsum_rewrite]
    _ ≤ ∑ i : Fin P.n,
          |f (tags i) * (α (P.pts i.succ) - α (P.pts i.castSucc)) -
            (f (tags i) * α' (tags i)) *
              (P.pts i.succ - P.pts i.castSucc)| := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin P.n,
          C * eta * (P.pts i.succ - P.pts i.castSucc) := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        let c := cellMVTTag P hαderiv i
        have hc_eq :
            α (P.pts i.succ) - α (P.pts i.castSucc) =
              α' c * (P.pts i.succ - P.pts i.castSucc) := by
          simpa [c] using cellMVTTag_increment_eq P hαderiv i
        have htagI : tags i ∈ Set.Icc a b := tag_mem_Icc P htags i
        have hcI : c ∈ Set.Icc a b := by
          simpa [c] using cellMVTTag_mem_Icc P hαderiv i
        have hdist : |c - tags i| < delta := by
          have hle : |c - tags i| ≤ P.mesh := by
            simpa [c] using tag_mvt_distance_le_mesh P htags hαderiv i
          exact lt_of_le_of_lt hle hmesh
        have hosc : |α' c - α' (tags i)| ≤ eta :=
          hα'osc c hcI (tags i) htagI hdist
        have hfbound : |f (tags i)| ≤ C := hbound (tags i) htagI
        have hlen_nonneg : 0 ≤ P.pts i.succ - P.pts i.castSucc :=
          sub_nonneg.mpr (le_of_lt (P.strict_mono Fin.castSucc_lt_succ))
        have hprod :
            |f (tags i)| * |α' c - α' (tags i)| *
                (P.pts i.succ - P.pts i.castSucc) ≤
              C * eta * (P.pts i.succ - P.pts i.castSucc) := by
          have hmul₁ :
              |f (tags i)| * |α' c - α' (tags i)| ≤ C * eta :=
            mul_le_mul hfbound hosc (abs_nonneg _) hC
          exact mul_le_mul_of_nonneg_right hmul₁ hlen_nonneg
        have hterm_eq :
            f (tags i) * (α (P.pts i.succ) - α (P.pts i.castSucc)) -
                (f (tags i) * α' (tags i)) *
                  (P.pts i.succ - P.pts i.castSucc) =
              f (tags i) * (α' c - α' (tags i)) *
                (P.pts i.succ - P.pts i.castSucc) := by
          rw [hc_eq]
          ring
        rw [hterm_eq, abs_mul, abs_mul, abs_of_nonneg hlen_nonneg]
        exact hprod
    _ = C * eta * (b - a) := by
        rw [← Finset.mul_sum]
        rw [partition_length_sum P]
/-! ## Ordinary interval integral as RS integral with identity integrator -/

theorem solution {f α α' : ℝ → ℝ} {a b C eta delta : ℝ}
    (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (hα'osc :
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
        |x - y| < delta → |α' x - α' y| ≤ eta)
    (hmesh : P.mesh < delta)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc a b → |f x| ≤ C)
    (hC : 0 ≤ C) :
    |taggedSum P tags f α -
        taggedSum P tags (fun x => f x * α' x) (fun x => x)| ≤
      C * eta * (b - a) := by
  exact source_taggedSum_derivative_identity_abs_le P tags htags hαderiv hα'osc hmesh hbound hC
