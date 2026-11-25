-- Prove2me | solution 1 for SNumbers.half_le_entropyNumber_id_of_not_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:22:20.873072+00:00
-- url     : https://prove2.me/submissions/f9433354-ddb6-438e-8d94-2d289a709cf1

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
public import Theorems.Thm_SNumbers_le_entropyNumber_of_separated

set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
open MeasureTheory
namespace SNumbers
theorem _root_.solution (X : Type u) [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (hX : ¬FiniteDimensional 𝕜 X) (n : ℕ) :
    1 / 2 ≤ entropyNumber (ContinuousLinearMap.id 𝕜 X) n := by
  classical
  -- For every `R > 1`, `1 / (2R) ≤ eₙ(id_X)`.
  have key : ∀ R : ℝ, 1 < R → 1 / R / 2 ≤ entropyNumber (ContinuousLinearMap.id 𝕜 X) n := by
    intro R hR
    have hR0 : 0 < R := by linarith
    have hc : 1 < ‖(((1 + R) / 2 : ℝ) : 𝕜)‖ := by
      rw [RCLike.norm_ofReal, abs_of_pos (by linarith)]; linarith
    have hcR : ‖(((1 + R) / 2 : ℝ) : 𝕜)‖ < R := by
      rw [RCLike.norm_ofReal, abs_of_pos (by linarith)]; linarith
    obtain ⟨f, hf_norm, hf_sep⟩ := exists_seq_norm_le_one_le_norm_sub' hc hcR hX
    set g : ℕ → X := fun k => ((R⁻¹ : ℝ) : 𝕜) • f k with hg
    have hcR' : ‖((R⁻¹ : ℝ) : 𝕜)‖ = R⁻¹ := by
      rw [RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hR0)]
    have hsep : ∀ k l : ℕ, k ≠ l → 1 / R ≤ dist (g k) (g l) := by
      intro k l hkl
      rw [hg, dist_eq_norm, ← smul_sub, norm_smul, hcR', one_div]
      exact le_mul_of_one_le_right (inv_pos.mpr hR0).le (hf_sep hkl)
    set P : Finset X := (Finset.range (2 ^ n + 1)).image g with hP
    have hinj : Set.InjOn g (Finset.range (2 ^ n + 1) : Set ℕ) := by
      intro k _ l _ hkl
      by_contra hne
      have := hsep k l hne
      rw [hkl, dist_self] at this
      exact absurd this (not_le.mpr (by positivity))
    have hcard : 2 ^ n < P.card := by
      rw [hP, Finset.card_image_of_injOn hinj, Finset.card_range]; omega
    have hsub : ↑P ⊆ ⇑(ContinuousLinearMap.id 𝕜 X) '' Metric.closedBall 0 1 := by
      intro z hz
      rw [hP, Finset.coe_image] at hz
      obtain ⟨k, -, rfl⟩ := hz
      refine ⟨g k, ?_, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right, hg, norm_smul, hcR']
      exact (inv_mul_le_one₀ hR0).mpr (hf_norm k)
    have hP_sep : ∀ z ∈ P, ∀ z' ∈ P, z ≠ z' → 1 / R ≤ dist z z' := by
      intro z hz z' hz' hne
      rw [hP, Finset.mem_image] at hz hz'
      obtain ⟨k, -, rfl⟩ := hz
      obtain ⟨l, -, rfl⟩ := hz'
      exact hsep k l (fun h => hne (by rw [h]))
    exact le_entropyNumber_of_separated hsub hcard hP_sep
  -- Let `R = 1 + ε` tend to `1`.
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h := key (1 + ε) (by linarith)
  have hle : 1 / 2 - ε ≤ 1 / (1 + ε) / 2 := by
    rw [div_div, show (1 : ℝ) / 2 - ε = (1 - 2 * ε) / 2 by ring, div_le_div_iff₀ (by norm_num)
      (by positivity)]
    nlinarith
  linarith
end SNumbers
