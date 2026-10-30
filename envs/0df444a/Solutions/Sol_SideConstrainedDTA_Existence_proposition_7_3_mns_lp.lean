-- Prove2me | solution 1 for SideConstrainedDTA.Existence.proposition_7_3_mns_lp
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T23:35:34.034492+00:00
-- url     : https://prove2.me/submissions/13171b20-8b94-456e-b519-b1f8d55ffa9b

import Mathlib
import Definitions.Def_SideConstrainedDTA_Existence_Setting

open MeasureTheory Set Filter Topology

open SideConstrainedDTA.Existence

theorem solution {I W E : Type*} [Fintype I] [Fintype W] [DecidableEq I]
    [DecidableEq W] (N : Model I W E) (hN : N.Standing) (Φ : (W → ℝ → ℝ) → W → ℝ → ℝ)
    (h : W → ℝ → ℝ) :
    IsSCDE N Φ (capFeasible N) (devMNS N) h → IsSCDE N Φ (capFeasible N) (devLP N) h := by
  rintro ⟨hS, hE⟩
  refine ⟨hS, fun p t ht x hx => hE p t ht x ?_⟩
  obtain ⟨hcom, hx⟩ := hx
  refine ⟨hcom, fun δ hδ ε hε => ?_⟩
  obtain ⟨γ, hγm, hγb, hγs, hγi, hγA⟩ := hx δ hδ ε hε
  exact ⟨γ, hγm, hγb, hγs, hγi, hγA.1, Or.inr hγA.2⟩
