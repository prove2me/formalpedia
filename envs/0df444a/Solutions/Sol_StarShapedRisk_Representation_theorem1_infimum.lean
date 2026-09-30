-- Prove2me | solution 1 for StarShapedRisk.Representation.theorem1_infimum
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:15:41.662738+00:00
-- url     : https://prove2.me/submissions/9315ff4f-1915-4cca-99e5-cb1c30a43d9f

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
    IsStarShapedRiskMeasure 𝒳 (riskInf 𝒳 ρ) := by
  have hb (X : 𝒳.carrier) := (risk_bounds 𝒳 ρ (fun i => (hρ i).1) X).2
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro X Y hXY
    exact ciInf_mono (hb Y) (fun i => (hρ i).1.1 X Y hXY)
  · intro X m
    change (⨅ i, ρ i (X - 𝒳.const m)) = (⨅ i, ρ i X) - m
    apply le_antisymm
    · apply (le_sub_iff_add_le).mpr
      apply le_ciInf
      intro i
      have hh := ciInf_le (hb (X - 𝒳.const m)) i
      rw [(hρ i).1.2.1] at hh
      linarith
    · apply le_ciInf
      intro i
      rw [(hρ i).1.2.1]
      exact sub_le_sub_right (ciInf_le (hb X) i) m
  · change (⨅ i, ρ i 0) = 0
    have hz (i : I) : ρ i 0 = 0 := (hρ i).1.2.2
    simp [hz]
  · intro X t ht
    change t * (⨅ i, ρ i X) ≤ (⨅ i, ρ i (t • X))
    apply le_ciInf
    intro i
    exact (mul_le_mul_of_nonneg_left (ciInf_le (hb X) i) (lt_trans zero_lt_one ht).le).trans
      ((hρ i).2 X t ht)


