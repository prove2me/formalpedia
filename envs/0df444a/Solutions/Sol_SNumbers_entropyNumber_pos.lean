-- Prove2me | solution 1 for SNumbers.entropyNumber_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:50:53.28425+00:00
-- url     : https://prove2.me/submissions/8a399192-d044-423b-ad9f-24f7ab41059f

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
public import Theorems.Thm_SNumbers_le_entropyNumber_of_separated
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_entropyNumber_zero_op
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] John.rankOneSA_apply
attribute [local simp] SNumbers.Complexification.adjoint_complexify
attribute [local simp] SNumbers.Complexification.complexify_conj
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_snd
attribute [local simp] SNumbers.Complexification.norm_complexify
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] SNumbers.entropyNumber_zero_op
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] Submodule.liftQL_mkQL



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
namespace SNumbers
theorem _root_.solution {S : X →L[𝕜] Y} (hS : S ≠ 0) (n : ℕ) : 0 < entropyNumber S n := by
  classical
  -- A unit vector `x₀` with `S x₀ ≠ 0`.
  obtain ⟨x, hx⟩ : ∃ x, S x ≠ 0 := by
    by_contra h
    push Not at h
    exact hS (ContinuousLinearMap.ext h)
  have hx0 : x ≠ 0 := fun h => hx (by rw [h, map_zero])
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set x₀ : X := ((‖x‖⁻¹ : ℝ) : 𝕜) • x with hx₀
  have hx₀_norm : ‖x₀‖ = 1 := by
    rw [hx₀, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hxpos),
      inv_mul_cancel₀ hxpos.ne']
  set v : Y := S x₀ with hv
  have hv0 : v ≠ 0 := by
    rw [hv, hx₀, map_smul]
    exact smul_ne_zero (by simpa using hxpos.ne') hx
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  -- The points `f k = (k / 2ⁿ) • v`.
  set f : ℕ → Y := fun k => (((k : ℝ) / 2 ^ n : ℝ) : 𝕜) • v with hf
  have hdist : ∀ k l : ℕ, dist (f k) (f l) = |(k : ℝ) - l| / 2 ^ n * ‖v‖ := by
    intro k l
    rw [hf, dist_eq_norm, ← sub_smul, norm_smul, ← RCLike.ofReal_sub, RCLike.norm_ofReal,
      ← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n)]
  have hsep : ∀ k l : ℕ, k ≠ l → ‖v‖ / 2 ^ n ≤ dist (f k) (f l) := by
    intro k l hkl
    rw [hdist]
    have h1 : (1 : ℝ) ≤ |(k : ℝ) - l| := by
      have : (k : ℤ) ≠ l := by exact_mod_cast hkl
      have h := Int.one_le_abs (sub_ne_zero.mpr this)
      exact_mod_cast h
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  set P : Finset Y := (Finset.range (2 ^ n + 1)).image f with hP
  have hinj : Set.InjOn f (Finset.range (2 ^ n + 1) : Set ℕ) := by
    intro k _ l _ hkl
    by_contra hne
    have := hsep k l hne
    rw [hkl, dist_self] at this
    exact absurd this (not_le.mpr (by positivity))
  have hcard : 2 ^ n < P.card := by
    rw [hP, Finset.card_image_of_injOn hinj, Finset.card_range]; omega
  have hsub : ↑P ⊆ ⇑S '' Metric.closedBall 0 1 := by
    intro z hz
    rw [hP, Finset.coe_image] at hz
    obtain ⟨k, hk, rfl⟩ := hz
    have hk' : (k : ℝ) ≤ 2 ^ n := by
      have : k ≤ 2 ^ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      exact_mod_cast this
    refine ⟨(((k : ℝ) / 2 ^ n : ℝ) : 𝕜) • x₀, ?_, by rw [map_smul]⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hx₀_norm, mul_one,
      RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
    exact div_le_one_of_le₀ hk' (by positivity)
  have hP_sep : ∀ z ∈ P, ∀ z' ∈ P, z ≠ z' → ‖v‖ / 2 ^ n ≤ dist z z' := by
    intro z hz z' hz' hne
    rw [hP, Finset.mem_image] at hz hz'
    obtain ⟨k, -, rfl⟩ := hz
    obtain ⟨l, -, rfl⟩ := hz'
    exact hsep k l (fun h => hne (by rw [h]))
  have := le_entropyNumber_of_separated hsub hcard hP_sep
  have hpos : 0 < ‖v‖ / 2 ^ n / 2 := by positivity
  linarith
end SNumbers
