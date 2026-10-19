-- Prove2me | solution 1 for SoficGroups.ExceptionalRankOffset.exists_common_log_rank_offsets_tendsto_zero_except
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/dafe5206-3e8a-4697-9e34-b6240000bbd7

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_rankDropCount_nonneg_and_le
import Theorems.Thm_SoficGroups_abs_log_one_sub_div_tendsto_zero
import Theorems.Thm_SoficGroups_ExceptionalRankOffset_exists_common_log_rank_offset_except

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.ExceptionalRankOffset
open Filter Topology
open scoped BigOperators
namespace SoficGroups.ExceptionalRankOffset
theorem _root_.solution
    (ι : ℕ → Type*)
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (G : (n : ℕ) → Finset (ι n))
    (x y : (n : ℕ) → ι n → ℝ)
    (eta H N : ℕ → ℝ) (C : ℝ)
    (hx : ∀ n i, i ∈ G n → 0 < x n i)
    (heta0 : ∀ n, 0 ≤ eta n)
    (heta1 : ∀ n, eta n < 1)
    (hH : ∀ n, 0 < H n)
    (hN : ∀ n, 0 < N n)
    (hcard : ∀ n, ((G n).card : ℝ) ≤ C * N n)
    (hcomparison : ∀ n i, i ∈ G n →
      (1 - eta n) * x n i ≤ y n i)
    (heta : Tendsto eta atTop (nhds 0))
    (hratio : Tendsto (fun n => eta n / H n) atTop (nhds 0))
    (hexceptions : Tendsto
      (fun n =>
        (((Finset.univ : Finset (ι n)) \ G n).card : ℝ) / N n)
      atTop (nhds 0)) :
    ∃ r : ℕ → ℝ,
      (∀ n, r n ∈ Set.Ico 0 (H n)) ∧
        Tendsto
          (fun n =>
            SoficGroups.rankDropCount
              (fun i => Real.log (x n i))
              (fun i => Real.log (y n i)) (H n) (r n) / N n)
          atTop (nhds 0) := by
  have hwitness : ∀ n, ∃ r ∈ Set.Ico 0 (H n),
      SoficGroups.rankDropCount
          (fun i => Real.log (x n i))
          (fun i => Real.log (y n i)) (H n) r ≤
        ((G n).card : ℝ) * |Real.log (1 - eta n)| / H n +
          (((Finset.univ : Finset (ι n)) \ G n).card : ℝ) := by
    intro n
    exact exists_common_log_rank_offset_except
      (G n) (x n) (y n) (eta n) (H n)
      (hx n) (heta0 n) (heta1 n) (hH n) (hcomparison n)
  choose r hr hbound using hwitness
  refine ⟨r, hr, ?_⟩
  have hlog := SoficGroups.abs_log_one_sub_div_tendsto_zero
    eta H heta0 hH heta hratio
  have hscaled : Tendsto
      (fun n => C * (|Real.log (1 - eta n)| / H n))
      atTop (nhds 0) := by
    simpa using Filter.Tendsto.const_mul C hlog
  have hlimit : Tendsto
      (fun n =>
        C * (|Real.log (1 - eta n)| / H n) +
          (((Finset.univ : Finset (ι n)) \ G n).card : ℝ) / N n)
      atTop (nhds 0) := by
    simpa only [add_zero] using hscaled.add hexceptions
  have hnonnegative : ∀ n,
      0 ≤ SoficGroups.rankDropCount
        (fun i => Real.log (x n i))
        (fun i => Real.log (y n i)) (H n) (r n) / N n := by
    intro n
    exact div_nonneg
      (SoficGroups.rankDropCount_nonneg_and_le
        (fun i => Real.log (x n i))
        (fun i => Real.log (y n i)) (H n) (r n)).1
      (hN n).le
  have hupper : ∀ n,
      SoficGroups.rankDropCount
          (fun i => Real.log (x n i))
          (fun i => Real.log (y n i)) (H n) (r n) / N n ≤
        C * (|Real.log (1 - eta n)| / H n) +
          (((Finset.univ : Finset (ι n)) \ G n).card : ℝ) / N n := by
    intro n
    calc
      SoficGroups.rankDropCount
          (fun i => Real.log (x n i))
          (fun i => Real.log (y n i)) (H n) (r n) / N n ≤
        (((G n).card : ℝ) * |Real.log (1 - eta n)| / H n +
          (((Finset.univ : Finset (ι n)) \ G n).card : ℝ)) / N n :=
          (div_le_div_iff_of_pos_right (hN n)).2 (hbound n)
      _ = (((G n).card : ℝ) / N n) *
            (|Real.log (1 - eta n)| / H n) +
          (((Finset.univ : Finset (ι n)) \ G n).card : ℝ) / N n := by
            ring
      _ ≤ C * (|Real.log (1 - eta n)| / H n) +
          (((Finset.univ : Finset (ι n)) \ G n).card : ℝ) / N n := by
            apply add_le_add
            · apply mul_le_mul_of_nonneg_right
                ((div_le_iff₀ (hN n)).2 (hcard n))
              exact div_nonneg (abs_nonneg _) (hH n).le
            · exact le_refl _
  exact squeeze_zero'
    (Filter.Eventually.of_forall hnonnegative)
    (Filter.Eventually.of_forall hupper)
    hlimit
end SoficGroups.ExceptionalRankOffset
