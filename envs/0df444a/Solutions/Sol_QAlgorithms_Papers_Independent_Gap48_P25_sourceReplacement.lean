-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P25.sourceReplacement
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T23:27:22.484896+00:00
-- url     : https://prove2.me/submissions/7f7a4c53-0f03-465a-8d77-b302f148c57c

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

open QAlgorithms.Papers.Independent.Gap48.P25
noncomputable section


open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- Eq.(4), PDF p.8: uniform source replacement and preservation under every
linear subsequent transformation, including channels with joint Bob–Eve output. -/
theorem solution {S H V : Type*} [Fintype S] [Nonempty S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [AddCommMonoid V] [Module ℂ V] (psi : S → H) (hpsi : ∀ s, ‖psi s‖ = 1)
    (L : (H →L[ℂ] H) →ₗ[ℂ] V) :
    ‖sourceReplacementVector psi‖ = 1 ∧
    (∀ s, ‖sourceReplacementVector psi s‖^2 = (Fintype.card S : ℝ)⁻¹ ∧
      ((Real.sqrt (Fintype.card S : ℝ)) : ℂ) • sourceReplacementVector psi s = psi s ∧
      replacementBlock psi s = ((Fintype.card S : ℂ)⁻¹) • InnerProductSpace.rankOne ℂ (psi s) (psi s) ∧
      L (replacementBlock psi s) = ((Fintype.card S : ℂ)⁻¹) • L (InnerProductSpace.rankOne ℂ (psi s) (psi s))) ∧
    replacementReduction psi = ((Fintype.card S : ℂ)⁻¹) •
      ∑ s, InnerProductSpace.rankOne ℂ (psi s) (psi s) := by
  set n : ℝ := (Fintype.card S : ℝ) with hn
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  set c : ℝ := Real.sqrt n with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 hn0
  have hcc : c * c = n := Real.mul_self_sqrt hn0.le
  have hv : ∀ s, sourceReplacementVector psi s = ((c:ℂ)⁻¹) • psi s := by
    intro s; first | rfl | simp [sourceReplacementVector, hc, hn]
  have hnorm : ∀ s, ‖sourceReplacementVector psi s‖^2 = n⁻¹ := by
    intro s
    rw [hv, norm_smul, hpsi, mul_one, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc0, inv_pow, sq, hcc]
  have hblock : ∀ s, replacementBlock psi s =
      ((Fintype.card S : ℂ)⁻¹) • InnerProductSpace.rankOne ℂ (psi s) (psi s) := by
    intro s
    unfold replacementBlock
    rw [hv]
    ext y
    simp only [InnerProductSpace.rankOne_apply, ContinuousLinearMap.smul_apply, inner_smul_left,
      smul_smul]
    congr 1
    have : (Fintype.card S : ℂ) = ((c*c : ℝ) : ℂ) := by rw [hcc, hn]; push_cast; rfl
    rw [this]
    have hc' : (c:ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    simp only [map_inv₀, Complex.conj_ofReal]
    push_cast
    field_simp
  refine ⟨?_, fun s => ⟨hnorm s, ?_, hblock s, ?_⟩, ?_⟩
  · have h2 : ‖sourceReplacementVector psi‖^2 = 1 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp_rw [hnorm]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn]
      field_simp
    have h0 := norm_nonneg (sourceReplacementVector psi)
    nlinarith [h2]
  · rw [hv, smul_smul]
    have hc' : (c:ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    rw [show ((Real.sqrt n : ℝ) : ℂ) = (c:ℂ) from rfl, mul_inv_cancel₀ hc', one_smul]
  · rw [hblock, map_smul]
  · unfold replacementReduction
    simp_rw [hblock]
    rw [Finset.smul_sum]




