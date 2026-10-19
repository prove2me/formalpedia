-- Prove2me | solution 1 for SoficGroups.ErshovJaikinFiniteSpectral.hasPropertyT_of_geometric_finite_averaging
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/ba87d456-365b-4bfe-99a9-cff544f70fe1

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ErshovJaikinFiniteSpectral
open Filter Topology
universe u v
namespace SoficGroups.ErshovJaikinFiniteSpectral
theorem _root_.solution
    {G : Type u} [Group G] (S : Finset G) (q : ℝ)
    (hq1 : q < 1)
    (haverage :
      ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] (π : SoficGroups.UnitaryRepresentation G H),
        ∃ A : H →L[ℂ] H,
          (∀ (x : H) (n : ℕ),
            dist ((A : H → H)^[n] x)
                ((A : H → H)^[n + 1] x) ≤
              (∑ g ∈ S, ‖π g x - x‖) * q ^ n) ∧
          (∀ x : H, A x = x → ∀ g : G, π g x = x)) :
    SoficGroups.HasPropertyT.{u, v} G := by
  classical
  let δ : ℝ := (1 - q) / (2 * (S.card + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    apply div_pos (sub_pos.mpr hq1)
    positivity
  refine ⟨⟨{
    generators := S
    kazhdanConstant := δ
    positive := hδ
    invariant := ?_
  }⟩⟩
  intro H _ _ _ π ξ hξ hsmall
  obtain ⟨A, hstep, hfixed⟩ := haverage H π
  let C : ℝ := ∑ g ∈ S, ‖π g ξ - ξ‖
  let f : ℕ → H := fun n => ((A : H → H)^[n]) ξ
  have hgeometric : ∀ n : ℕ,
      dist (f n) (f (n + 1)) ≤ C * q ^ n := by
    intro n
    exact hstep ξ n
  have hcauchy : CauchySeq f :=
    cauchySeq_of_le_geometric q C hq1 hgeometric
  obtain ⟨η, hηlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hηfixed : A η = η :=
    isFixedPt_of_tendsto_iterate hηlim A.continuous.continuousAt
  have hdist : dist ξ η ≤ C / (1 - q) := by
    simpa [f] using
      (dist_le_of_le_geometric_of_tendsto₀ q C hq1 hgeometric hηlim)
  have hsum : C ≤ S.card * δ := by
    dsimp [C]
    calc
      (∑ g ∈ S, ‖π g ξ - ξ‖) ≤ ∑ _g ∈ S, δ := by
        exact Finset.sum_le_sum fun g hg => (hsmall g hg).le
      _ = S.card * δ := by simp
  have hhalf : C < (1 - q) / 2 := by
    calc
      C ≤ S.card * δ := hsum
      _ < (1 - q) / 2 := by
        dsimp [δ]
        have hpos : 0 < (1 - q) := sub_pos.mpr hq1
        have hc : (S.card : ℝ) < (S.card : ℝ) + 1 := by linarith
        have hcpos : 0 < (S.card : ℝ) + 1 := by positivity
        rw [show (2 * (↑S.card + 1) : ℝ) =
          2 * ((S.card : ℝ) + 1) by norm_cast]
        calc
          (S.card : ℝ) *
              ((1 - q) / (2 * ((S.card : ℝ) + 1))) =
            ((1 - q) / 2) *
              ((S.card : ℝ) / ((S.card : ℝ) + 1)) := by
                field_simp
          _ < ((1 - q) / 2) * 1 := by
            apply mul_lt_mul_of_pos_left
              (div_lt_one hcpos |>.mpr hc)
            positivity
          _ = (1 - q) / 2 := mul_one _
  have hηne : η ≠ 0 := by
    intro hzero
    subst η
    have hone : dist ξ (0 : H) = 1 := by simpa using hξ
    rw [hone] at hdist
    have hden : 0 < 1 - q := sub_pos.mpr hq1
    have hlt : C / (1 - q) < 1 / 2 :=
      (div_lt_iff₀ hden).mpr (by nlinarith [hhalf])
    linarith
  exact ⟨η, hηne, hfixed η hηfixed⟩
end SoficGroups.ErshovJaikinFiniteSpectral
