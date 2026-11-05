-- Prove2me | solution 1 for ShortWDRODual.MaxCost.example_2_sel
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:15:18.397829+00:00
-- url     : https://prove2.me/submissions/e7e84bf3-1b47-41bd-b5e3-58514aa749b7

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_MaxCost_Setting
import Theorems.Thm_BertsekasShreve_AnalyticSelection_lower_semianalytic_selection

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.MaxCost
open scoped ENNReal

theorem solution {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] (Phat : Measure X) [IsProbabilityMeasure Phat] :
    Sel Phat := by
  -- a Polish space is a Borel space in the sense of Bertsekas–Shreve (Definition 7.7)
  have hB : BertsekasShreve.AnalyticSelection.IsBorelSpace X := by
    letI := TopologicalSpace.upgradeIsCompletelyMetrizable X
    exact ⟨⟨X, inferInstance, inferInstance, inferInstance, Set.univ, MeasurableSet.univ,
      ⟨(Homeomorph.Set.univ X).symm⟩⟩⟩
  intro E hE hgraph
  set D : Set (X × X) := ShortWDRODual.IP.graph E with hDdef
  have hD : AnalyticSet D := hgraph.analyticSet
  let F : D → EReal := fun _ => 0
  have hF : BertsekasShreve.AnalyticSelection.IsLowerSemianalytic D F := by
    refine ⟨hD, fun c => ?_⟩
    by_cases h : (0 : EReal) < (c : EReal)
    · have : Subtype.val '' {x : D | F x < (c : EReal)} = D := by
        ext p
        constructor
        · rintro ⟨q, -, rfl⟩
          exact q.2
        · intro hp
          exact ⟨⟨p, hp⟩, h, rfl⟩
      rw [this]
      exact hD
    · have : Subtype.val '' {x : D | F x < (c : EReal)} = ∅ := by
        ext p
        constructor
        · rintro ⟨q, hq, rfl⟩
          exact absurd hq h
        · intro hp
          exact absurd hp (Set.notMem_empty p)
      rw [this]
      exact MeasureTheory.analyticSet_empty
  obtain ⟨-, -, hb⟩ :=
    BertsekasShreve.AnalyticSelection.lower_semianalytic_selection D hD F hF
  obtain ⟨φ, hφ, hφm, -⟩ := hb 1 one_pos
  have hfst : ∀ xh, xh ∈ Prod.fst '' D := fun xh => by
    obtain ⟨x, hx⟩ := (hE xh).2
    exact ⟨(xh, x), hx, rfl⟩
  refine ⟨fun xh => φ ⟨xh, hfst xh⟩, ?_, fun xh => hφ ⟨xh, hfst xh⟩⟩
  intro s hs
  have h := hφm.2 s hs Phat inferInstance
  have hpre : (fun xh => φ ⟨xh, hfst xh⟩) ⁻¹' s = Subtype.val '' (φ ⁻¹' s) := by
    ext xh
    constructor
    · intro hx
      exact ⟨⟨xh, hfst xh⟩, hx, rfl⟩
    · rintro ⟨⟨y, hy⟩, hys, rfl⟩
      exact hys
  rw [hpre]
  exact h
