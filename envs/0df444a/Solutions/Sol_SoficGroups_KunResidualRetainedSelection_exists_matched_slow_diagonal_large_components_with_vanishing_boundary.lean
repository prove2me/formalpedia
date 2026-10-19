-- Prove2me | solution 1 for SoficGroups.KunResidualRetainedSelection.exists_matched_slow_diagonal_large_components_with_vanishing_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/e8abe6fe-288a-40eb-b385-20bc741a86ac

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_exists_matched_slow_diagonal_word_errors
import Theorems.Thm_SoficGroups_matchedRadiusBad_card_le
import Theorems.Thm_SoficGroups_matched_eventually_exists_good_vertex
import Theorems.Thm_SoficGroups_KunResidualRetainedSelection_exists_matchedRetained_parts_with_vanishing_boundary_and_bad_density

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualRetainedSelection
open Filter Topology
open scoped BigOperators Pointwise symmDiff
namespace SoficGroups.KunResidualRetainedSelection
theorem _root_.solution
    {K : Type*} [Group K] [Infinite K] [DecidableEq K]
    (S : Finset K) (hS : 1 ∈ S)
    (hgen : Subgroup.closure (S : Set K) = ⊤)
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    {ι κ : Type*} [Fintype κ]
    (σ : (n : ℕ) → κ → Equiv.Perm (V n))
    (U : ∀ n, Finset (V n)) (hU : ∀ n, (U n).Nonempty)
    (P Q : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (hRne : ∀ n, (R n).Nonempty)
    (D : ∀ n, Finset (V n) → Finset (V n))
    (hD : ∀ n C, C ∈ R n → D n C ∈ (Q n).parts)
    (hmajor : ∀ n C, C ∈ R n →
      (D n C).card < 2 * (C ∩ D n C).card)
    (hdiscard : Tendsto
      (fun n =>
        (((U n \ SoficGroups.matchedRetainedSupport (R n)).card : ℝ) /
          (U n).card)) atTop (𝓝 0))
    (hsymm : Tendsto
      (fun n =>
        ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) / (U n).card)
      atTop (𝓝 0))
    (I : ℕ → Finset ι)
    (w : ∀ n, ι → Equiv.Perm (V n))
    (hword : ∀ k, Tendsto
      (fun n =>
        ((∑ i ∈ I k,
          (SoficGroups.partitionWordCrossing (Q n) (w n i)).card : ℕ) :
            ℝ) / (U n).card)
      atTop (𝓝 0))
    (B : ∀ n, ℕ → Finset (V n))
    (hbad : ∀ k, Tendsto
      (fun n => (((U n ∩ B n k).card : ℝ) / (U n).card))
      atTop (𝓝 0))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts, (SoficGroups.boundary (σ n) C : ℝ)) /
          (U n).card) atTop (𝓝 0))
    (hrealize : ∀ n k (C : Finset (V n)), C ∈ R n →
      ∀ x ∈ C,
        x ∉ SoficGroups.matchedRadiusBad
          (P n) (I k) (w n) (B n k) →
          ∃ f : K → V n,
            Set.MapsTo f (↑(S ^ (k / 2)) : Set K) (↑C : Set (V n)) ∧
              Set.InjOn f (↑(S ^ (k / 2)) : Set K)) :
    ∃ (r : ℕ → ℕ) (C : ∀ n, Finset (V n)),
      Tendsto r atTop atTop ∧
        (∀ n, C n ∈ R n) ∧
        Tendsto
          (fun n =>
            (SoficGroups.boundary (σ n) (C n) : ℝ) / (C n).card)
          atTop (𝓝 0) ∧
        Tendsto
          (fun n =>
            (((C n ∩
              SoficGroups.matchedRadiusBad
                (P n) (I (r n)) (w n) (B n (r n))).card : ℝ) /
                  (C n).card))
          atTop (𝓝 0) ∧
        Tendsto (fun n => (C n).card) atTop atTop := by
  obtain ⟨r, hr, herror⟩ :=
    SoficGroups.exists_matched_slow_diagonal_word_errors
      U P Q R hR D hD hmajor hdiscard hsymm I w hword B hbad
  let B' : ∀ n, Finset (V n) := fun n =>
    SoficGroups.matchedRadiusBad (P n) (I (r n)) (w n) (B n (r n))
  have hB' : Tendsto
      (fun n => (((U n ∩ B' n).card : ℝ) / (U n).card))
      atTop (𝓝 0) := by
    refine squeeze_zero (fun n => by positivity) ?_ herror
    intro n
    have hcard :
        ((U n ∩ B' n).card : ℝ) ≤
          ((∑ i ∈ I (r n),
            (SoficGroups.partitionWordCrossing
              (P n) (w n i)).card : ℕ) : ℝ) +
            ((U n ∩ B n (r n)).card : ℝ) := by
      have h := SoficGroups.matchedRadiusBad_card_le
        (P n) (I (r n)) (w n) (B n (r n))
      have h' :
          (U n ∩
            SoficGroups.matchedRadiusBad
              (P n) (I (r n)) (w n) (B n (r n))).card ≤
                (∑ i ∈ I (r n),
                  (SoficGroups.partitionWordCrossing
                    (P n) (w n i)).card) +
                  (U n ∩ B n (r n)).card := by
        omega
      dsimp [B']
      exact_mod_cast h'
    exact div_le_div_of_nonneg_right hcard (by positivity)
  obtain ⟨C, hC, hCboundary, hCerror⟩ :=
    exists_matchedRetained_parts_with_vanishing_boundary_and_bad_density
      σ U hU P R hR hRne hdiscard B' hB' hboundary
  have hCnonempty (n : ℕ) : (C n).Nonempty :=
    (P n).nonempty_of_mem_parts (hR n (hC n))
  have hgood : ∀ᶠ n in atTop, ∃ x ∈ C n, x ∉ B' n :=
    SoficGroups.matched_eventually_exists_good_vertex
      C B' hCnonempty hCerror
  have hhalf : Tendsto (fun n => r n / 2) atTop atTop :=
    (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hr
  have hclosure :
      (Subgroup.closure (S : Set K) : Set K).Infinite := by
    simpa [hgen] using (Set.infinite_univ (α := K))
  have hlarge : Tendsto (fun n => (C n).card) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hhalf
    filter_upwards [hgood] with n hn
    obtain ⟨x, hx, hx'⟩ := hn
    obtain ⟨f, hf, hfinj⟩ :=
      hrealize n (r n) (C n) (hC n) x hx hx'
    exact (Nat.le_succ (r n / 2)).trans
      ((Finset.add_one_le_card_pow hS hclosure (r n / 2)).trans
        (Finset.card_le_card_of_injOn f hf hfinj))
  exact ⟨r, C, hr, hC, hCboundary, hCerror, hlarge⟩
end SoficGroups.KunResidualRetainedSelection
