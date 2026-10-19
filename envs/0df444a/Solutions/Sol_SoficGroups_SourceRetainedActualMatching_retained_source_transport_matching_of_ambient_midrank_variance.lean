-- Prove2me | solution 1 for SoficGroups.SourceRetainedActualMatching.retained_source_transport_matching_of_ambient_midrank_variance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/e7783369-6646-49d8-a138-ae22a0ab7831

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_finpartition_dominant_matching_injOn
import Theorems.Thm_SoficGroups_SourceCompressionMatching_symmDiff_density_tendsto_zero_of_log_rank_bounds
import Theorems.Thm_SoficGroups_SourceCompressionRetainedDiscard_retained_missing_density_tendsto_zero
import Theorems.Thm_SoficGroups_KunCommonRankArcInvariance_exists_common_rank_invariance_of_midrank_variance
import Theorems.Thm_SoficGroups_SourceRetainedActualMatching_retained_transport_component_matching_bounds

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceRetainedActualMatching
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.SourceRetainedActualMatching
theorem _root_.solution
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    (κ : Type*)
    (Q A : (n : ℕ) → Finpartition
      (Finset.univ : Finset (V n)))
    (T : (n : ℕ) → κ → Equiv.Perm (V n))
    (H r eta : ℕ → ℝ)
    (hHpos : ∀ n, 0 < H n)
    (hHzero : Tendsto H atTop (nhds 0))
    (heta0 : ∀ n, 0 ≤ eta n)
    (hetazero : Tendsto eta atTop (nhds 0))
    (hvariance : Tendsto
      (fun n =>
        (∑ C ∈ (A n).parts,
          (C.card : ℝ) *
            SoficGroups.midrankVariance
              (SoficGroups.componentRankMassList C
                (logarithmicComponentRank (Q n) (H n) (r n)))) /
                  Fintype.card (V n))
      atTop (nhds 0))
    (hcross : ∀ i : κ, Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing
          (A n) (T n i).symm).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0))
    (hoverlap : ∀ i : κ, Tendsto
      (fun n =>
        ((∑ C ∈ SoficGroups.insufficientOverlapComponents
          (SoficGroups.transportedUnivFinpartition (Q n) (T n i))
          (Q n) (eta n), C.card : ℕ) : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0)) :
    ∀ i : κ,
      (∀ n, retainedTransportedComponents
        (Q n) (T n i) (H n) (r n) (eta n) ⊆
          (SoficGroups.transportedUnivFinpartition
            (Q n) (T n i)).parts) ∧
      (∀ n C, C ∈ retainedTransportedComponents
        (Q n) (T n i) (H n) (r n) (eta n) →
          SoficGroups.maximumOverlapPart (Q n) C ∈ (Q n).parts) ∧
      (∀ n, eta n ≤ (1 : ℝ) / 2 →
        2 * (Real.exp (H n) - 1 + 2 * eta n) < 1 →
          ∀ C, C ∈ retainedTransportedComponents
            (Q n) (T n i) (H n) (r n) (eta n) →
              (SoficGroups.maximumOverlapPart (Q n) C).card <
                2 * (C ∩ SoficGroups.maximumOverlapPart
                  (Q n) C).card) ∧
      Tendsto
        (fun n =>
          (((Finset.univ : Finset (V n)) \
            SoficGroups.matchedRetainedSupport
              (retainedTransportedComponents
                (Q n) (T n i) (H n) (r n) (eta n))).card : ℝ) /
              Fintype.card (V n))
        atTop (nhds 0) ∧
      Tendsto
        (fun n =>
          ((∑ C ∈ retainedTransportedComponents
            (Q n) (T n i) (H n) (r n) (eta n),
              (C ∆ SoficGroups.maximumOverlapPart (Q n) C).card :
                ℕ) : ℝ) / Fintype.card (V n))
        atTop (nhds 0) ∧
      (∀ n, 2 * (Real.exp (H n) - 1 + 2 * eta n) < 1 →
        Set.InjOn (SoficGroups.maximumOverlapPart (Q n))
          ((retainedTransportedComponents
            (Q n) (T n i) (H n) (r n) (eta n) :
              Finset (Finset (V n))) :
                Set (Finset (V n)))) := by
  let b : (n : ℕ) → V n → ℤ :=
    fun n => logarithmicComponentRank (Q n) (H n) (r n)
  obtain ⟨_j, _hj, _homit, hrank⟩ :=
    SoficGroups.KunCommonRankArcInvariance.exists_common_rank_invariance_of_midrank_variance
      A b (fun n i => (T n i).symm) hvariance hcross
  intro i
  let P : (n : ℕ) → Finpartition
      (Finset.univ : Finset (V n)) :=
    fun n => SoficGroups.transportedUnivFinpartition (Q n) (T n i)
  let R : (n : ℕ) → Finset (Finset (V n)) :=
    fun n => retainedTransportedComponents
      (Q n) (T n i) (H n) (r n) (eta n)
  have hparts (n : ℕ) : R n ⊆ (P n).parts := by
    exact Finset.sdiff_subset
  have htarget (n : ℕ) (C : Finset (V n)) (hC : C ∈ R n) :
      SoficGroups.maximumOverlapPart (Q n) C ∈ (Q n).parts :=
    (retained_transport_component_matching_bounds
      (Q n) (T n i) (H n) (r n) (eta n) (hHpos n) C hC).1
  have hmajor (n : ℕ)
      (_heta : eta n ≤ (1 : ℝ) / 2)
      (hsmall : 2 * (Real.exp (H n) - 1 + 2 * eta n) < 1)
      (C : Finset (V n)) (hC : C ∈ R n) :
      (SoficGroups.maximumOverlapPart (Q n) C).card <
        2 * (C ∩ SoficGroups.maximumOverlapPart (Q n) C).card :=
    (retained_transport_component_matching_bounds
      (Q n) (T n i) (H n) (r n) (eta n) (hHpos n) C hC).2.2.2 hsmall
  have hbound (n : ℕ) (C : Finset (V n)) (hC : C ∈ R n) :
      ((C ∆ SoficGroups.maximumOverlapPart (Q n) C).card : ℝ) ≤
        (Real.exp (H n) - 1 + 2 * eta n) * (C.card : ℝ) :=
    (retained_transport_component_matching_bounds
      (Q n) (T n i) (H n) (r n) (eta n) (hHpos n) C hC).2.2.1.le
  have hdiscard :
      Tendsto
        (fun n =>
          (((Finset.univ : Finset (V n)) \
            SoficGroups.matchedRetainedSupport (R n)).card : ℝ) /
              Fintype.card (V n))
        atTop (nhds 0) := by
    exact
      SoficGroups.SourceCompressionRetainedDiscard.retained_missing_density_tendsto_zero
        V P Q (fun n => T n i) b eta hetazero
        (hoverlap i) (hrank i)
  have hsymmetric :
      Tendsto
        (fun n =>
          ((∑ C ∈ R n,
            (C ∆ SoficGroups.maximumOverlapPart (Q n) C).card :
              ℕ) : ℝ) / Fintype.card (V n))
        atTop (nhds 0) := by
    have hfull (n : ℕ) :
        (Finset.univ : Finset (V n)).Nonempty :=
      Finset.univ_nonempty
    simpa only [Finset.card_univ] using
      SoficGroups.SourceCompressionMatching.symmDiff_density_tendsto_zero_of_log_rank_bounds
        (V := V) (fun n => (Finset.univ : Finset (V n))) hfull
        P R hparts (fun n => SoficGroups.maximumOverlapPart (Q n))
        H eta (fun n => (hHpos n).le) heta0 hHzero hetazero
        hbound
  refine ⟨hparts, htarget, hmajor, hdiscard, hsymmetric, ?_⟩
  intro n hsmall
  exact SoficGroups.finpartition_dominant_matching_injOn
    (P n) (R n) (hparts n)
    (SoficGroups.maximumOverlapPart (Q n))
    (fun C hC =>
      (retained_transport_component_matching_bounds
        (Q n) (T n i) (H n) (r n) (eta n)
        (hHpos n) C hC).2.2.2 hsmall)
end SoficGroups.SourceRetainedActualMatching
