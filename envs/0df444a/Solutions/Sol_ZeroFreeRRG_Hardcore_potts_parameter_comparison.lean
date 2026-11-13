-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_parameter_comparison
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:53:51.805617+00:00
-- url     : https://prove2.me/submissions/8ace4577-ae35-418e-bd59-5f950ad72d47

import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_contraction_data
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_transport_expectations
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_edge_properties
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_edge_nonconstant
import Theorems.Thm_ZeroFreeRRG_Hardcore_entropy_contraction
import Theorems.Thm_ZeroFreeRRG_Hardcore_entropy_positive_mean_one
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ZeroFreeRRG.Hardcore

private theorem entropy_nonnegative {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : Ω → ℝ) (hE : ∀ᵐ ω ∂μ, 0 ≤ E ω)
    (hInt : Integrable E μ) (hEnt : Integrable (fun ω => xlogx (E ω)) μ)
    (hmean : (∫ ω, E ω ∂μ) = 1) : 0 ≤ ∫ ω, xlogx (E ω) ∂μ := by
  have hgap : 0 ≤ᵐ[μ] (fun ω => xlogx (E ω) - E ω + 1) := by
    filter_upwards [hE] with ω hω
    dsimp [xlogx]
    linarith [Real.self_sub_one_le_mul_log hω]
  have hh := integral_nonneg_of_ae hgap
  have heq : (∫ ω, xlogx (E ω) - E ω + 1 ∂μ) =
      (∫ ω, xlogx (E ω) ∂μ) - (∫ ω, E ω ∂μ) + (1:ℝ) := by
    have hi := integral_add (hEnt.sub hInt) (integrable_const (1:ℝ))
    simp only [Pi.add_apply, Pi.sub_apply] at hi
    rw [hi, integral_sub hEnt hInt, integral_const]
    simp only [probReal_univ, one_smul]
  rw [heq,hmean] at hh
  linarith

theorem solution (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q) (β' β : ℝ)
    (hβ' : 0 ≤ β') (hlt : β' < β) (hβ : β < 1)
    (hrs : VariationalRS (.potts q) d β') :
    Condition1 (.potts q) d β ∧ VariationalRS (.potts q) d β := by
  have hb0 : 0 ≤ β := le_of_lt (lt_of_le_of_lt hβ' hlt)
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hden : (q:ℝ)-1+β' ≠ 0 := by linarith
  have hnum : β'-1 ≠ 0 := by linarith
  have hk' : (β'-1)/((q:ℝ)-1+β') ≠ 0 := div_ne_zero hnum hden
  let c := ((β-1)/((q:ℝ)-1+β)) / ((β'-1)/((q:ℝ)-1+β'))
  have hk : c*((β'-1)/((q:ℝ)-1+β')) = (β-1)/((q:ℝ)-1+β) := by
    dsimp [c]
    exact div_mul_cancel₀ _ hk'
  have hdpos : 0 < (d:ℝ)/2 := by
    have hd' : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    positivity
  have hcomparison (ν : ProbabilityMeasure (Fin q → ℝ)) (hν : ν ∈ cavityLaws (.potts q) β) :
      betheK (.potts q) β d ν ≤ 0 ∧
      (ν ≠ diracPi (.potts q) β → betheK (.potts q) β d ν < 0) := by
    obtain ⟨hc0,hc1,ν',hν',hne,hmap,hvert,hedge⟩ := potts_contraction_data q d hq β β' hβ' hlt hβ ν hν
    change ProbabilityMeasure (Fin q → ℝ) at ν'
    change 0 < c at hc0
    change c < 1 at hc1
    have htr := potts_transport_expectations q d hq β β' c hb0 hβ' hk ν ν' hν hmap
    obtain ⟨hmean,hE,hInt,hEnt,hEntC⟩ := potts_edge_properties q hq β c hb0 ν hν
    let μ := (ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ))
    let E : (Fin q → ℝ) × (Fin q → ℝ) → ℝ := fun p => edgeFactor (.potts q) β p.1 p.2
    have hcontract := entropy_contraction μ E c hc0 hc1 hE hEnt hEntC
    have hnonneg := entropy_nonnegative μ E hE hInt hEnt hmean
    have hrs' := hrs ν' hν'
    unfold betheK at hrs' ⊢
    change (∫ ys : Fin d → Fin q → ℝ, xlogx (vertexFactor (.potts q) β' d ys)
        ∂(Measure.pi fun _ : Fin d => ((ν' : ProbabilityMeasure (Fin q → ℝ)) : Measure (Fin q → ℝ)))) - (d:ℝ)/2 *
      (∫ ys : (Fin q → ℝ) × (Fin q → ℝ), xlogx (edgeFactor (.potts q) β' ys.1 ys.2)
        ∂(((ν' : ProbabilityMeasure (Fin q → ℝ)) : Measure (Fin q → ℝ)).prod ((ν' : ProbabilityMeasure (Fin q → ℝ)) : Measure (Fin q → ℝ)))) ≤ 0 at hrs'
    rw [htr.1, htr.2] at hrs'
    constructor
    · have hmul : (d:ℝ)/2 * (∫ p, xlogx (1-c+c*E p) ∂μ) ≤
          (d:ℝ)/2 * (∫ p, xlogx (E p) ∂μ) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hdpos)
        nlinarith [hcontract.1, mul_nonneg (le_of_lt (sub_pos.mpr hc1)) hnonneg]
      change (∫ xs : Fin d → Fin q → ℝ, xlogx (vertexFactor (.potts q) β d xs)
          ∂(Measure.pi fun _ : Fin d => (ν : Measure (Fin q → ℝ)))) -
        (d:ℝ)/2 * (∫ p, xlogx (E p) ∂μ) ≤ 0
      change _ - (d:ℝ)/2 * (∫ p, xlogx (1-c+c*E p) ∂μ) ≤ 0 at hrs'
      linarith
    · intro hn
      have hpos := potts_edge_nonconstant q hq β hb0 hβ ν hν hn
      have hepos := entropy_positive_mean_one μ E hE hInt hEnt hmean hpos
      have hltE : (∫ p, xlogx (1-c+c*E p) ∂μ) < (∫ p, xlogx (E p) ∂μ) := by
        nlinarith [mul_pos (sub_pos.mpr hc1) hepos, hcontract.1]
      have hmul := mul_lt_mul_of_pos_left hltE hdpos
      change (∫ xs : Fin d → Fin q → ℝ, xlogx (vertexFactor (.potts q) β d xs)
          ∂(Measure.pi fun _ : Fin d => (ν : Measure (Fin q → ℝ)))) -
        (d:ℝ)/2 * (∫ p, xlogx (E p) ∂μ) < 0
      change _ - (d:ℝ)/2 * (∫ p, xlogx (1-c+c*E p) ∂μ) ≤ 0 at hrs'
      linarith
  exact ⟨fun ν hν hn => (hcomparison ν hν).2 hn, fun ν hν => (hcomparison ν hν).1⟩
