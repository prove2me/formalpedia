-- Prove2me | solution 1 for SoficGroups.KunActualCanonicalSelectedPruning.exists_actual_uniformly_expanding_pruned_selected_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/14116d9b-67e8-4906-9d7e-dac9d48c846c

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunCompletedPrunedComponent_exists_completed_pruned_expander
import Theorems.Thm_SoficGroups_MatchedComponentExitBudget_pruned_component_card_tendsto_atTop

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualCanonicalSelectedPruning
open Filter Topology
open SoficGroups.MatchedComponentCompletion
namespace SoficGroups.KunActualCanonicalSelectedPruning
theorem _root_.solution
    {K J : Type*} [Group K] [Group J]
    (A : SoficGroups.SoficApproximation (K × J))
    (S : Finset K)
    (ν : ℕ → ℕ)
    (Q : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (A.model (ν n)).size)))
    (C : (n : ℕ) → Finset (Fin (A.model (ν n)).size))
    (hC : ∀ n, C n ∈ (Q n).parts)
    (hlarge : Tendsto (fun n => (C n).card) atTop atTop)
    (γ : ℝ) (hγ : 0 < γ)
    (a : ℕ → ℝ)
    (ha : Tendsto a atTop (nhds 0))
    (hadd : ∀ n,
      ∀ E : Finset {x : Fin (A.model (ν n)).size // x ∈ C n},
        γ * min (E.card : ℝ)
            ((Fintype.card
              {x : Fin (A.model (ν n)).size // x ∈ C n} : ℝ) -
                E.card) -
          a n * Fintype.card
            {x : Fin (A.model (ν n)).size // x ∈ C n} ≤
          (SoficGroups.boundary
            (fun i : ↥S =>
              completedRestriction
                ((A.model (ν n)).action ((i : K), (1 : J)))
                (C n)) E : ℝ)) :
    ∃ (N : ℕ)
      (D : (n : ℕ) → Finset
        {x : Fin (A.model (ν (n + N))).size // x ∈ C (n + N)})
      (τ : (n : ℕ) → ↥S → Equiv.Perm
        {x : {y : Fin (A.model (ν (n + N))).size //
                y ∈ C (n + N)} //
          x ∈ (Finset.univ \ D n :
            Finset {y : Fin (A.model (ν (n + N))).size //
              y ∈ C (n + N)})}),
      (∀ n,
        (Finset.univ \ D n :
          Finset {x : Fin (A.model (ν (n + N))).size //
            x ∈ C (n + N)}).Nonempty) ∧
      Tendsto
        (fun n => ((D n).card : ℝ) / (C (n + N)).card)
        atTop (nhds 0) ∧
      Tendsto
        (fun n =>
          (Finset.univ \ D n :
            Finset {x : Fin (A.model (ν (n + N))).size //
              x ∈ C (n + N)}).card)
        atTop atTop ∧
      (∀ n (i : ↥S)
        (x : {y : Fin (A.model (ν (n + N))).size //
          y ∈ C (n + N)})
        (hx : x ∈ (Finset.univ \ D n :
          Finset {y : Fin (A.model (ν (n + N))).size //
            y ∈ C (n + N)}))
        (_hi : completedRestriction
          ((A.model (ν (n + N))).action ((i : K), (1 : J)))
          (C (n + N)) x ∈
            (Finset.univ \ D n :
              Finset {y : Fin (A.model (ν (n + N))).size //
                y ∈ C (n + N)})),
        ((τ n i ⟨x, hx⟩ :
          {z : {y : Fin (A.model (ν (n + N))).size //
                    y ∈ C (n + N)} //
            z ∈ (Finset.univ \ D n :
              Finset {y : Fin (A.model (ν (n + N))).size //
                y ∈ C (n + N)})}) :
          {y : Fin (A.model (ν (n + N))).size //
            y ∈ C (n + N)}) =
            completedRestriction
              ((A.model (ν (n + N))).action ((i : K), (1 : J)))
              (C (n + N)) x) ∧
      (∀ n,
        ∀ E : Finset
          {x : {y : Fin (A.model (ν (n + N))).size //
                  y ∈ C (n + N)} //
            x ∈ (Finset.univ \ D n :
              Finset {y : Fin (A.model (ν (n + N))).size //
                y ∈ C (n + N)})},
          (γ / 2) * min (E.card : ℝ)
            ((Fintype.card
              {x : {y : Fin (A.model (ν (n + N))).size //
                      y ∈ C (n + N)} //
                x ∈ (Finset.univ \ D n :
                  Finset {y : Fin (A.model (ν (n + N))).size //
                    y ∈ C (n + N)})} : ℝ) - E.card) ≤
            (SoficGroups.boundary (τ n) E : ℝ)) := by
  classical
  let ell : ℝ := γ / 2
  have hgap : ell < γ := by
    dsimp [ell]
    linarith
  have hgapPositive : 0 < γ - ell := sub_pos.mpr hgap
  let c : ℝ :=
    2 * (2 * (γ - ell) + (Fintype.card ↥S : ℝ))
  have hc : 0 < c := by
    dsimp [c]
    have hcard : (0 : ℝ) ≤ Fintype.card ↥S := by
      exact Nat.cast_nonneg _
    nlinarith
  have htarget : 0 < (γ - ell) ^ 2 / c :=
    div_pos (sq_pos_of_pos hgapPositive) hc
  have hsmallEvent : ∀ᶠ n in atTop,
      a n < (γ - ell) ^ 2 / c :=
    ha.eventually (gt_mem_nhds htarget)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmallEvent
  have hsmall (n : ℕ) :
      2 * a (n + N) *
          (2 * (γ - ell) + (Fintype.card ↥S : ℝ)) ≤
        (γ - ell) ^ 2 := by
    have hratio : a (n + N) < (γ - ell) ^ 2 / c :=
      hN (n + N) (by omega)
    have hbound : a (n + N) * c < (γ - ell) ^ 2 :=
      (lt_div_iff₀ hc).mp hratio
    calc
      2 * a (n + N) *
          (2 * (γ - ell) + (Fintype.card ↥S : ℝ)) =
        a (n + N) * c := by
          dsimp [c]
          ring
      _ ≤ (γ - ell) ^ 2 := hbound.le
  have hstage (n : ℕ) :
      ∃ (D : Finset
          {x : Fin (A.model (ν (n + N))).size //
            x ∈ C (n + N)})
        (τ : ↥S → Equiv.Perm
          {x : {y : Fin (A.model (ν (n + N))).size //
                  y ∈ C (n + N)} //
            x ∈ (Finset.univ \ D :
              Finset {y : Fin (A.model (ν (n + N))).size //
                y ∈ C (n + N)})}),
        2 * D.card ≤ (C (n + N)).card ∧
        (D.card : ℝ) ≤
          a (n + N) * (C (n + N)).card / (γ - ell) ∧
        (∀ (i : ↥S)
          (x : {y : Fin (A.model (ν (n + N))).size //
            y ∈ C (n + N)})
          (hx : x ∈ (Finset.univ \ D :
            Finset {y : Fin (A.model (ν (n + N))).size //
              y ∈ C (n + N)}))
          (_hi : completedRestriction
            ((A.model (ν (n + N))).action ((i : K), (1 : J)))
            (C (n + N)) x ∈
              (Finset.univ \ D :
                Finset {y : Fin (A.model (ν (n + N))).size //
                  y ∈ C (n + N)})),
          ((τ i ⟨x, hx⟩ :
            {z : {y : Fin (A.model (ν (n + N))).size //
                      y ∈ C (n + N)} //
              z ∈ (Finset.univ \ D :
                Finset {y : Fin (A.model (ν (n + N))).size //
                  y ∈ C (n + N)})}) :
            {y : Fin (A.model (ν (n + N))).size //
              y ∈ C (n + N)}) =
              completedRestriction
                ((A.model (ν (n + N))).action ((i : K), (1 : J)))
                (C (n + N)) x) ∧
        (∀ E : Finset
          {x : {y : Fin (A.model (ν (n + N))).size //
                  y ∈ C (n + N)} //
            x ∈ (Finset.univ \ D :
              Finset {y : Fin (A.model (ν (n + N))).size //
                y ∈ C (n + N)})},
          ell * min (E.card : ℝ)
            ((Fintype.card
              {x : {y : Fin (A.model (ν (n + N))).size //
                      y ∈ C (n + N)} //
                x ∈ (Finset.univ \ D :
                  Finset {y : Fin (A.model (ν (n + N))).size //
                    y ∈ C (n + N)})} : ℝ) - E.card) ≤
            (SoficGroups.boundary τ E : ℝ)) := by
    simpa only [Fintype.card_coe] using
      SoficGroups.KunCompletedPrunedComponent.exists_completed_pruned_expander
        (fun i : ↥S =>
          completedRestriction
            ((A.model (ν (n + N))).action ((i : K), (1 : J)))
            (C (n + N)))
        γ ell (a (n + N)) hgap (hadd (n + N)) (hsmall n)
  choose D τ hhalf hbound hagree hexpand using hstage
  have hnonempty (n : ℕ) :
      (Finset.univ \ D n :
        Finset {x : Fin (A.model (ν (n + N))).size //
          x ∈ C (n + N)}).Nonempty := by
    have hCpositive : 0 < (C (n + N)).card :=
      ((Q (n + N)).nonempty_of_mem_parts (hC (n + N))).card_pos
    have hpositive :
        0 < (Finset.univ \ D n :
          Finset {x : Fin (A.model (ν (n + N))).size //
            x ∈ C (n + N)}).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ (D n)),
        Finset.card_univ, Fintype.card_coe]
      have hh := hhalf n
      omega
    exact Finset.card_pos.mp hpositive
  have hshift : Tendsto (fun n : ℕ => n + N) atTop atTop :=
    tendsto_add_atTop_nat N
  have haupper : Tendsto
      (fun n => a (n + N) / (γ - ell))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, zero_div] using
      (ha.comp hshift).div_const (γ - ell)
  have hdeleted : Tendsto
      (fun n => ((D n).card : ℝ) / (C (n + N)).card)
      atTop (nhds 0) := by
    apply squeeze_zero
      (fun n => by positivity)
      (fun n => ?_)
      haupper
    have hCpositive : (0 : ℝ) < (C (n + N)).card := by
      exact_mod_cast
        ((Q (n + N)).nonempty_of_mem_parts (hC (n + N))).card_pos
    calc
      ((D n).card : ℝ) / (C (n + N)).card ≤
        (a (n + N) * (C (n + N)).card /
          (γ - ell)) / (C (n + N)).card :=
          div_le_div_of_nonneg_right (hbound n) hCpositive.le
      _ = a (n + N) / (γ - ell) := by
          field_simp [hCpositive.ne', hgapPositive.ne']
  have hshiftlarge :
      Tendsto (fun n => (C (n + N)).card) atTop atTop := by
    simpa only [Function.comp_def] using hlarge.comp hshift
  have hzlarge : Tendsto
      (fun n =>
        (Finset.univ \ D n :
          Finset {x : Fin (A.model (ν (n + N))).size //
            x ∈ C (n + N)}).card)
      atTop atTop := by
    apply SoficGroups.MatchedComponentExitBudget.pruned_component_card_tendsto_atTop
      (fun n => {x : Fin (A.model (ν (n + N))).size //
        x ∈ C (n + N)}) D
    · simpa only [Fintype.card_coe] using hshiftlarge
    · simpa only [Fintype.card_coe] using hdeleted
  refine ⟨N, D, τ, hnonempty, hdeleted, hzlarge,
    hagree, ?_⟩
  simpa only [ell] using hexpand
end SoficGroups.KunActualCanonicalSelectedPruning
