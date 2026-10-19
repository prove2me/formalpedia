-- Prove2me | solution 1 for SoficGroups.SourceCompressionRetainedDiscard.retained_missing_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/1a86a567-6704-44e0-94a1-1ff94a595909

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceCompressionRetainedDiscard_retained_missing_card_le_overlap_add_twice_rankChanging

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionRetainedDiscard
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.SourceCompressionRetainedDiscard
theorem _root_.solution
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (P Q : (n : ℕ) → Finpartition
      (Finset.univ : Finset (V n)))
    (T : (n : ℕ) → Equiv.Perm (V n))
    (b : (n : ℕ) → V n → ℤ) (eta : ℕ → ℝ)
    (heta : Tendsto eta atTop (nhds 0))
    (hoverlap : Tendsto
      (fun n =>
        ((∑ C ∈ SoficGroups.insufficientOverlapComponents
          (P n) (Q n) (eta n), C.card : ℕ) : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0))
    (hrank : Tendsto
      (fun n =>
        ((SoficGroups.RankArcCharging.rankChangingArc
          (Finset.univ : Finset (V n)) (b n) (T n).symm).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (((Finset.univ : Finset (V n)) \
          SoficGroups.matchedRetainedSupport
            (retainedComponents (P n) (Q n) (T n) (b n)
              (eta n))).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0) := by
  have hhalf : ∀ᶠ n in atTop, eta n < (1 : ℝ) / 2 :=
    heta.eventually (gt_mem_nhds (by norm_num))
  have htwice : Tendsto
      (fun n => (2 : ℝ) *
        (((SoficGroups.RankArcCharging.rankChangingArc
          (Finset.univ : Finset (V n)) (b n) (T n).symm).card : ℝ) /
            Fintype.card (V n)))
      atTop (nhds 0) := by
    simpa using hrank.const_mul 2
  have hupper : Tendsto
      (fun n =>
        ((∑ C ∈ SoficGroups.insufficientOverlapComponents
          (P n) (Q n) (eta n), C.card : ℕ) : ℝ) /
            Fintype.card (V n) +
          (2 : ℝ) *
            (((SoficGroups.RankArcCharging.rankChangingArc
              (Finset.univ : Finset (V n)) (b n) (T n).symm).card : ℝ) /
                Fintype.card (V n)))
      atTop (nhds 0) := by
    simpa only [zero_add] using hoverlap.add htwice
  refine squeeze_zero'
    (Eventually.of_forall fun n => by positivity) ?_ hupper
  filter_upwards [hhalf] with n hn
  have hnat := retained_missing_card_le_overlap_add_twice_rankChanging
    (P n) (Q n) (T n) (b n) (eta n) hn.le
  have hreal :
      (((Finset.univ : Finset (V n)) \
        SoficGroups.matchedRetainedSupport
          (retainedComponents (P n) (Q n) (T n) (b n)
            (eta n))).card : ℝ) ≤
        ((∑ C ∈ SoficGroups.insufficientOverlapComponents
          (P n) (Q n) (eta n), C.card : ℕ) : ℝ) +
          2 * ((SoficGroups.RankArcCharging.rankChangingArc
            (Finset.univ : Finset (V n)) (b n) (T n).symm).card : ℝ) := by
    exact_mod_cast hnat
  calc
    (((Finset.univ : Finset (V n)) \
      SoficGroups.matchedRetainedSupport
        (retainedComponents (P n) (Q n) (T n) (b n)
          (eta n))).card : ℝ) / Fintype.card (V n) ≤
        (((∑ C ∈ SoficGroups.insufficientOverlapComponents
          (P n) (Q n) (eta n), C.card : ℕ) : ℝ) +
          2 * ((SoficGroups.RankArcCharging.rankChangingArc
            (Finset.univ : Finset (V n)) (b n) (T n).symm).card : ℝ)) /
            Fintype.card (V n) :=
      div_le_div_of_nonneg_right hreal (by positivity)
    _ = ((∑ C ∈ SoficGroups.insufficientOverlapComponents
          (P n) (Q n) (eta n), C.card : ℕ) : ℝ) /
            Fintype.card (V n) +
          (2 : ℝ) *
            (((SoficGroups.RankArcCharging.rankChangingArc
              (Finset.univ : Finset (V n)) (b n) (T n).symm).card : ℝ) /
                Fintype.card (V n)) := by
      ring
end SoficGroups.SourceCompressionRetainedDiscard
