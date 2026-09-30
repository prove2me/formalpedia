-- Prove2me | solution 1 for StarShapedRisk.Representation.theorem1_average
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:15:44.029932+00:00
-- url     : https://prove2.me/submissions/686a455e-5b42-4951-91bc-f281fbca8511

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

open MeasureTheory

theorem solution {Ω : Type*} (𝒳 : PositionSpace Ω) {I : Type*} [MeasurableSpace I]
    (hI : ‹MeasurableSpace I› = ⊤) (μ : MeasureTheory.Measure I)
    [MeasureTheory.IsProbabilityMeasure μ]
    (ρ : I → 𝒳.carrier → ℝ) (hρ : ∀ i, IsStarShapedRiskMeasure 𝒳 (ρ i)) :
    IsStarShapedRiskMeasure 𝒳 (riskAverage 𝒳 μ ρ) := by
  have hint (X : 𝒳.carrier) : Integrable (fun i => ρ i X) μ := by
    have hm : Measurable (fun i => ρ i X) := by
      apply measurable_iff_comap_le.mpr
      rw [hI]
      exact le_top
    obtain ⟨⟨U, hU⟩, ⟨L, hL⟩⟩ := risk_bounds 𝒳 ρ (fun i => (hρ i).1) X
    apply Integrable.of_bound hm.aestronglyMeasurable (max |L| |U|)
    apply Filter.Eventually.of_forall
    intro i
    rw [Real.norm_eq_abs, abs_le]
    have hu := hU (Set.mem_range_self i)
    have hl := hL (Set.mem_range_self i)
    have h1 := le_max_left |L| |U|
    have h2 := le_max_right |L| |U|
    have h3 := neg_abs_le L
    have h4 := le_abs_self U
    constructor <;> linarith
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro X Y hXY
    exact integral_mono (hint Y) (hint X) (fun i => (hρ i).1.1 X Y hXY)
  · intro X m
    change (∫ i, ρ i (X - 𝒳.const m) ∂μ) = (∫ i, ρ i X ∂μ) - m
    have he : (fun i => ρ i (X - 𝒳.const m)) = fun i => ρ i X - m :=
      funext fun i => (hρ i).1.2.1 X m
    rw [he, integral_sub (hint X) (integrable_const m)]
    simp
  · change (∫ i, ρ i 0 ∂μ) = 0
    have he : (fun i => ρ i 0) = fun _ => (0:ℝ) := funext fun i => (hρ i).1.2.2
    rw [he]
    simp
  · intro X t ht
    change t * (∫ i, ρ i X ∂μ) ≤ (∫ i, ρ i (t • X) ∂μ)
    rw [← integral_const_mul]
    exact integral_mono ((hint X).const_mul t) (hint (t • X)) (fun i => (hρ i).2 X t ht)


