-- Prove2me | solution 1 for StarShapedRisk.Representation.theorem1_supremum
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:15:41.057507+00:00
-- url     : https://prove2.me/submissions/f8e93580-53a7-4216-bc2a-9ca0527a8096

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_RiskMeasure
import Definitions.Def_StarShapedRisk_Representation_Aggregation
set_option autoImplicit false
open StarShapedRisk.Representation
private theorem risk_bounds {Ω : Type*} (𝒳 : PositionSpace Ω) {I : Type*}
    (ρ : I → 𝒳.carrier → ℝ) (hρ : ∀ i, IsRiskMeasure 𝒳 (ρ i)) (X : 𝒳.carrier) :
    BddAbove (Set.range fun i => ρ i X) ∧ BddBelow (Set.range fun i => ρ i X) := by
  have hc (i : I) (m : ℝ) : ρ i (𝒳.const m) = m := by
    have he : (0 : 𝒳.carrier) - 𝒳.const (-m) = 𝒳.const m := by
      ext ω
      simp [PositionSpace.const]
    have hh := (hρ i).2.1 0 (-m)
    rw [he, (hρ i).2.2] at hh
    simpa using hh
  obtain ⟨C, hC⟩ := 𝒳.bounded X X.property
  constructor
  · refine ⟨C, ?_⟩
    rintro y ⟨i, rfl⟩
    calc
      ρ i X ≤ ρ i (𝒳.const C) := (hρ i).1 _ _ (fun ω => (abs_le.mp (hC ω)).2)
      _ = C := hc i C
  · refine ⟨-C, ?_⟩
    rintro y ⟨i, rfl⟩
    calc
      -C = ρ i (𝒳.const (-C)) := (hc i (-C)).symm
      _ ≤ ρ i X := (hρ i).1 _ _ (fun ω => (abs_le.mp (hC ω)).1)

theorem solution {Ω : Type*} (𝒳 : PositionSpace Ω) {I : Type*} [Nonempty I]
    (ρ : I → 𝒳.carrier → ℝ) (hρ : ∀ i, IsStarShapedRiskMeasure 𝒳 (ρ i)) :
    IsStarShapedRiskMeasure 𝒳 (riskSup 𝒳 ρ) := by
  have hb (X : 𝒳.carrier) := (risk_bounds 𝒳 ρ (fun i => (hρ i).1) X).1
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro X Y hXY
    exact ciSup_mono (hb X) (fun i => (hρ i).1.1 X Y hXY)
  · intro X m
    change (⨆ i, ρ i (X - 𝒳.const m)) = (⨆ i, ρ i X) - m
    apply le_antisymm
    · apply ciSup_le
      intro i
      rw [(hρ i).1.2.1]
      exact sub_le_sub_right (le_ciSup (hb X) i) m
    · apply (sub_le_iff_le_add).mpr
      apply ciSup_le
      intro i
      have hh := le_ciSup (hb (X - 𝒳.const m)) i
      rw [(hρ i).1.2.1] at hh
      linarith
  · change (⨆ i, ρ i 0) = 0
    have hz (i : I) : ρ i 0 = 0 := (hρ i).1.2.2
    simp [hz]
  · intro X t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    change t * (⨆ i, ρ i X) ≤ (⨆ i, ρ i (t • X))
    have hh : (⨆ i, ρ i X) ≤ (⨆ i, ρ i (t • X)) / t := by
      apply ciSup_le
      intro i
      apply (le_div_iff₀ ht0).mpr
      have hi := ((hρ i).2 X t ht).trans (le_ciSup (hb (t • X)) i)
      simpa [mul_comm] using hi
    have hh' := (le_div_iff₀ ht0).mp hh
    simpa [mul_comm] using hh'


