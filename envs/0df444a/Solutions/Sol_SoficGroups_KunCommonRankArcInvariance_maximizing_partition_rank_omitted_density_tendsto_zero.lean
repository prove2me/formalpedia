-- Prove2me | solution 1 for SoficGroups.KunCommonRankArcInvariance.maximizing_partition_rank_omitted_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/283c5374-017b-4138-9a1e-9a17f418c3bd

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_actual_weighted_midrank_dominant_mass_le
import Theorems.Thm_SoficGroups_RankArcCharging_card_sdiff_selectedRankSupport

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCommonRankArcInvariance
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunCommonRankArcInvariance
theorem _root_.solution
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (b : (n : ℕ) → V n → ℤ)
    (j : (n : ℕ) → Finset (V n) → ℤ)
    (hmax : ∀ n C, C ∈ (P n).parts →
      ∀ k ∈ C.image (b n),
        SoficGroups.componentRankMass C (b n) k ≤
          SoficGroups.componentRankMass C (b n) (j n C))
    (hvariance : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts,
          (C.card : ℝ) *
            SoficGroups.midrankVariance
              (SoficGroups.componentRankMassList C (b n))) /
                Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((((Finset.univ : Finset (V n)) \
          SoficGroups.RankArcCharging.selectedRankSupport
            (P n) (b n) (j n)).card : ℝ) /
              Fintype.card (V n)))
      atTop (nhds 0) := by
  classical
  have hupper : Tendsto
      (fun n =>
        (12 : ℝ) *
          ((∑ C ∈ (P n).parts,
            (C.card : ℝ) *
              SoficGroups.midrankVariance
                (SoficGroups.componentRankMassList C (b n))) /
                  Fintype.card (V n)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      ((tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (12 : ℝ)) atTop (nhds 12)).mul
          hvariance)
  refine squeeze_zero (fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ?_ hupper
  intro n
  have hfinite :=
    SoficGroups.actual_weighted_midrank_dominant_mass_le
      (P n).parts (fun C : Finset (V n) => C) (b n) (j n)
      (fun C hC => (P n).nonempty_of_mem_parts hC)
      (fun C hC => hmax n C hC)
  have hcard :=
    SoficGroups.RankArcCharging.card_sdiff_selectedRankSupport
      (P n) (b n) (j n)
  have hcast :
      ((((Finset.univ : Finset (V n)) \
        SoficGroups.RankArcCharging.selectedRankSupport
          (P n) (b n) (j n)).card : ℕ) : ℝ) =
        ∑ C ∈ (P n).parts,
          (((C.card -
            (C.filter fun x => b n x = j n C).card : ℕ) : ℝ)) := by
    exact_mod_cast hcard
  calc
    ((((Finset.univ : Finset (V n)) \
      SoficGroups.RankArcCharging.selectedRankSupport
        (P n) (b n) (j n)).card : ℝ) /
          Fintype.card (V n)) ≤
      (12 * (∑ C ∈ (P n).parts,
        (C.card : ℝ) *
          SoficGroups.midrankVariance
            (SoficGroups.componentRankMassList C (b n)))) /
              Fintype.card (V n) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      rw [hcast]
      exact hfinite
    _ = (12 : ℝ) *
        ((∑ C ∈ (P n).parts,
          (C.card : ℝ) *
            SoficGroups.midrankVariance
              (SoficGroups.componentRankMassList C (b n))) /
                Fintype.card (V n)) := by
      ring
end SoficGroups.KunCommonRankArcInvariance
