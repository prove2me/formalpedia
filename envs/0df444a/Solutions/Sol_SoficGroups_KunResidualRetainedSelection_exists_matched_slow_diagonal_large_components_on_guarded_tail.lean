-- Prove2me | solution 1 for SoficGroups.KunResidualRetainedSelection.exists_matched_slow_diagonal_large_components_on_guarded_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/33a93caa-e847-4875-aa74-778c12545f2f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunResidualRetainedSelection_exists_matched_slow_diagonal_large_components_with_vanishing_boundary
import Theorems.Thm_SoficGroups_KunResidualRetainedSelection_matchedRetained_parts_eventually_nonempty_of_discard

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
    (D : ∀ n, Finset (V n) → Finset (V n))
    (hD : ∀ n C, C ∈ R n → D n C ∈ (Q n).parts)
    (guard : ℕ → Prop)
    (hguard : ∀ᶠ n in atTop, guard n)
    (hmajor : ∀ n, guard n → ∀ C, C ∈ R n →
      (D n C).card < 2 * (C ∩ D n C).card)
    (hdiscard : Tendsto
      (fun n =>
        (((U n \ SoficGroups.matchedRetainedSupport (R n)).card : ℝ) /
          (U n).card)) atTop (𝓝 0))
    (hsymm : Tendsto
      (fun n =>
        ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) /
          (U n).card)
      atTop (𝓝 0))
    (I : ℕ → Finset ι)
    (w : ∀ n, ι → Equiv.Perm (V n))
    (hword : ∀ k, Tendsto
      (fun n =>
        ((∑ i ∈ I k,
          (SoficGroups.partitionWordCrossing (Q n) (w n i)).card :
            ℕ) : ℝ) / (U n).card)
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
            Set.MapsTo f (↑(S ^ (k / 2)) : Set K)
              (↑C : Set (V n)) ∧
              Set.InjOn f (↑(S ^ (k / 2)) : Set K))
    (N₀ : ℕ) :
    ∃ (N : ℕ) (r : ℕ → ℕ)
      (C : (n : ℕ) → Finset (V (n + N))),
      N₀ ≤ N ∧
        (∀ n, guard (n + N)) ∧
        Tendsto r atTop atTop ∧
        (∀ n, C n ∈ R (n + N)) ∧
        Tendsto
          (fun n =>
            (SoficGroups.boundary (σ (n + N)) (C n) : ℝ) /
              (C n).card)
          atTop (𝓝 0) ∧
        Tendsto
          (fun n =>
            (((C n ∩
              SoficGroups.matchedRadiusBad
                (P (n + N)) (I (r n)) (w (n + N))
                (B (n + N) (r n))).card : ℝ) /
                  (C n).card))
          atTop (𝓝 0) ∧
        Tendsto (fun n => (C n).card) atTop atTop := by
  have hretained :=
    matchedRetained_parts_eventually_nonempty_of_discard
      U hU R hdiscard
  obtain ⟨N₁, hN₁⟩ :=
    eventually_atTop.1 (hretained.and hguard)
  let N : ℕ := max N₀ N₁
  have htail (n : ℕ) :
      (R (n + N)).Nonempty ∧ guard (n + N) :=
    hN₁ (n + N) (by dsimp [N]; omega)
  have hshift : Tendsto (fun n : ℕ => n + N) atTop atTop :=
    tendsto_add_atTop_nat N
  have hdiscard' : Tendsto
      (fun n =>
        (((U (n + N) \
          SoficGroups.matchedRetainedSupport (R (n + N))).card : ℝ) /
            (U (n + N)).card))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using hdiscard.comp hshift
  have hsymm' : Tendsto
      (fun n =>
        ((∑ C ∈ R (n + N),
          (C ∆ D (n + N) C).card : ℕ) : ℝ) /
            (U (n + N)).card)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using hsymm.comp hshift
  have hword' (k : ℕ) : Tendsto
      (fun n =>
        ((∑ i ∈ I k,
          (SoficGroups.partitionWordCrossing
            (Q (n + N)) (w (n + N) i)).card : ℕ) : ℝ) /
              (U (n + N)).card)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using (hword k).comp hshift
  have hbad' (k : ℕ) : Tendsto
      (fun n =>
        (((U (n + N) ∩ B (n + N) k).card : ℝ) /
          (U (n + N)).card))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using (hbad k).comp hshift
  have hboundary' : Tendsto
      (fun n =>
        (∑ C ∈ (P (n + N)).parts,
          (SoficGroups.boundary (σ (n + N)) C : ℝ)) /
            (U (n + N)).card)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using hboundary.comp hshift
  obtain ⟨r, C, hr, hC, hCboundary, hCbad, hClarge⟩ :=
    exists_matched_slow_diagonal_large_components_with_vanishing_boundary
      S hS hgen
      (fun n => σ (n + N))
      (fun n => U (n + N))
      (fun n => hU (n + N))
      (fun n => P (n + N))
      (fun n => Q (n + N))
      (fun n => R (n + N))
      (fun n => hR (n + N))
      (fun n => (htail n).1)
      (fun n C => D (n + N) C)
      (fun n C hC => hD (n + N) C hC)
      (fun n C hC => hmajor (n + N) (htail n).2 C hC)
      hdiscard' hsymm' I
      (fun n => w (n + N))
      hword'
      (fun n k => B (n + N) k)
      hbad' hboundary'
      (fun n k C hC x hx hx' =>
        hrealize (n + N) k C hC x hx hx')
  refine ⟨N, r, C, ?_, (fun n => (htail n).2), hr, hC,
    hCboundary, hCbad, hClarge⟩
  exact le_max_left _ _
end SoficGroups.KunResidualRetainedSelection
