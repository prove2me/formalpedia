-- Prove2me | solution 1 for Thm11SourceRoute.pairwiseDisjoint_Ioo_of_radii_le_infsep_div_four
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:52:40.249955+00:00
-- url     : https://prove2.me/submissions/1b6dc921-8bdb-4bea-93dc-2552980678a5

import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute
end Thm11SourceRoute
section Thm11SourceRoute
open Thm11SourceRoute


theorem solution
    (S : Finset ℝ) (rho : ℝ → ℝ)
    (hrho_le :
      ∀ c : ℝ, c ∈ S →
        (S : Set ℝ).Nontrivial →
        rho c ≤ (S : Set ℝ).infsep / 4) :
    (↑S : Set ℝ).PairwiseDisjoint
      (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c)) := by
  classical
  rw [Set.PairwiseDisjoint]
  intro c hc d hd hne
  change Disjoint (Set.Ioo (c - rho c) (c + rho c))
    (Set.Ioo (d - rho d) (d + rho d))
  rw [Set.disjoint_left]
  intro x hxC hxD
  have hnontrivial : (S : Set ℝ).Nontrivial := ⟨c, hc, d, hd, hne⟩
  have hinf_pos : 0 < (S : Set ℝ).infsep := by
    exact (Finset.infsep_pos_iff_nontrivial S).2 hnontrivial
  have hcd_inf : (S : Set ℝ).infsep ≤ dist c d :=
    Set.infsep_le_dist_of_mem hc hd hne
  have hρc : rho c ≤ (S : Set ℝ).infsep / 4 := hrho_le c hc hnontrivial
  have hρd : rho d ≤ (S : Set ℝ).infsep / 4 := hrho_le d hd hnontrivial
  have hsumρ : rho c + rho d ≤ (S : Set ℝ).infsep / 2 := by
    linarith
  rcases le_total c d with hcd | hdc
  · have hcd_lt : c < d := lt_of_le_of_ne hcd hne
    have hdist_eq : dist c d = d - c := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hcd)]
      ring
    have hgap_lt : d - c < rho c + rho d := by
      linarith [hxC.2, hxD.1]
    have hgap_ge : (S : Set ℝ).infsep ≤ d - c := by
      simpa [hdist_eq] using hcd_inf
    linarith
  · have hdc_lt : d < c := lt_of_le_of_ne hdc hne.symm
    have hdist_eq : dist c d = c - d := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hdc)]
    have hgap_lt : c - d < rho c + rho d := by
      linarith [hxD.2, hxC.1]
    have hgap_ge : (S : Set ℝ).infsep ≤ c - d := by
      simpa [hdist_eq] using hcd_inf
    linarith
end Thm11SourceRoute
