-- Prove2me | solution 1 for VarStorageQN.LeastChange.proposition_A3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:35:38.047552+00:00
-- url     : https://prove2.me/submissions/b6fe2b31-3427-4981-804f-dd8170544587

import Mathlib
import Definitions.Def_VarStorageQN_LeastChange_Bracket

set_option autoImplicit false
open InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace
open VarStorageQN.LeastChange

namespace VSQhelpA3
open VarStorageQN.LeastChange

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem N_mul (w : H) (p q : ℝ) :
    ((1 : H →L[ℝ] H) + p • bracket w w) ∘L ((1 : H →L[ℝ] H) + q • bracket w w) =
      (1 : H →L[ℝ] H) + (p + q + p * q * ‖w‖ ^ 2) • bracket w w := by
  ext d
  simp only [bracket, rankOne_apply, add_apply, smul_apply, comp_apply, one_apply_eq_self,
    map_add, map_smul, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
  module

theorem N_symm (w : H) (p : ℝ) (x z : H) :
    ⟪((1 : H →L[ℝ] H) + p • bracket w w) x, z⟫_ℝ =
      ⟪x, ((1 : H →L[ℝ] H) + p • bracket w w) z⟫_ℝ := by
  simp only [bracket, rankOne_apply, add_apply, smul_apply, one_apply_eq_self,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  rw [real_inner_comm x w]
  ring

theorem exists_C (y s : H) (hs : s ≠ 0) (hpos : 0 < ⟪y, s⟫_ℝ) :
    ∃ C : H ≃L[ℝ] H, y = adjoint (C : H →L[ℝ] H) (C s) := by
  set a := ⟪y, s⟫_ℝ with ha
  have hn : 0 < ‖s‖ ^ 2 := by positivity
  set γ : ℝ := a / (2 * ‖s‖ ^ 2) with hγ
  have hγpos : 0 < γ := by positivity
  set μ : ℝ := 2 / a with hμ
  have hμpos : 0 < μ := by positivity
  set w : H := y - γ • s with hw
  have hws : ⟪w, s⟫_ℝ = a / 2 := by
    rw [hw, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, hγ]
    simp only [RCLike.conj_to_real]
    field_simp
    ring
  set ρ : ℝ := Real.sqrt (1 + μ / γ * ‖w‖ ^ 2) with hρ
  have hρ2 : ρ ^ 2 = 1 + μ / γ * ‖w‖ ^ 2 := by
    rw [hρ, Real.sq_sqrt]; positivity
  have hρ1 : 1 ≤ ρ := by
    rw [hρ]; apply Real.le_sqrt_of_sq_le; nlinarith [mul_nonneg (div_pos hμpos hγpos).le (sq_nonneg ‖w‖)]
  have hρpos : 0 < ρ := by linarith
  set θ : ℝ := (ρ - 1) / ‖w‖ ^ 2 with hθdef
  have hθ : θ * ‖w‖ ^ 2 = ρ - 1 := by
    by_cases hw0 : w = 0
    · have : ρ = 1 := by
        rw [hρ, hw0]; simp
      rw [this, hw0]; simp
    · have : ‖w‖ ^ 2 ≠ 0 := by positivity
      rw [hθdef]; field_simp
  set c : ℝ := Real.sqrt γ with hc
  have hcpos : 0 < c := Real.sqrt_pos.mpr hγpos
  have hc2 : c ^ 2 = γ := Real.sq_sqrt hγpos.le
  set φ : ℝ := -θ / ρ with hφ
  let N : H →L[ℝ] H := bracket w w
  let C : H →L[ℝ] H := c • ((1 : H →L[ℝ] H) + θ • N)
  let C' : H →L[ℝ] H := c⁻¹ • ((1 : H →L[ℝ] H) + φ • N)
  have hcomm : θ + φ + θ * φ * ‖w‖ ^ 2 = 0 := by
    rw [hφ]
    have : θ * (-θ / ρ) * ‖w‖ ^ 2 = -(θ * ‖w‖ ^ 2) * θ / ρ := by ring
    rw [this, hθ]
    field_simp
    ring
  have hL : C' ∘L C = 1 := by
    have := N_mul w φ θ
    show (c⁻¹ • ((1 : H →L[ℝ] H) + φ • N)) ∘L (c • ((1 : H →L[ℝ] H) + θ • N)) = 1
    rw [smul_comp, comp_smul, ← mul_smul, inv_mul_cancel₀ hcpos.ne', one_smul]
    rw [N_mul w φ θ]
    have : φ + θ + φ * θ * ‖w‖ ^ 2 = 0 := by linarith [hcomm]
    rw [this, zero_smul, add_zero]
  have hR : C ∘L C' = 1 := by
    show (c • ((1 : H →L[ℝ] H) + θ • N)) ∘L (c⁻¹ • ((1 : H →L[ℝ] H) + φ • N)) = 1
    rw [smul_comp, comp_smul, ← mul_smul, mul_inv_cancel₀ hcpos.ne', one_smul]
    rw [N_mul w θ φ, hcomm, zero_smul, add_zero]
  let E : H ≃L[ℝ] H := ContinuousLinearEquiv.equivOfInverse C C'
    (fun x => by simpa using congrArg (fun T => T x) hL)
    (fun x => by simpa using congrArg (fun T => T x) hR)
  refine ⟨E, ?_⟩
  have hE : (E : H →L[ℝ] H) = C := rfl
  have hself : adjoint C = C := by
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x z
    show ⟪(c • ((1 : H →L[ℝ] H) + θ • N)) x, z⟫_ℝ = ⟪x, (c • ((1 : H →L[ℝ] H) + θ • N)) z⟫_ℝ
    rw [smul_apply, smul_apply, inner_smul_left, inner_smul_right]
    simp only [RCLike.conj_to_real]
    rw [N_symm w θ x z]
  rw [hE, hself]
  have hCC : C ∘L C = γ • ((1 : H →L[ℝ] H) + (2 * θ + θ * θ * ‖w‖ ^ 2) • N) := by
    show (c • ((1 : H →L[ℝ] H) + θ • N)) ∘L (c • ((1 : H →L[ℝ] H) + θ • N)) = _
    rw [smul_comp, comp_smul, ← mul_smul, N_mul w θ θ, ← sq, hc2]
    congr 3
    ring
  have hy : C (C s) = y := by
    have h1 : C (C s) = (C ∘L C) s := rfl
    rw [h1, hCC]
    by_cases hw0 : w = 0
    · have : y = γ • s := by
        have := hw; rw [hw0] at this; exact (sub_eq_zero.mp this.symm)
      simp only [smul_apply, add_apply, one_apply_eq_self, N, bracket, rankOne_apply, hw0, inner_zero_left, zero_smul,
        smul_zero, add_zero, this]
    · have hκ : (2 * θ + θ * θ * ‖w‖ ^ 2) = μ / γ := by
        have hn0 : ‖w‖ ^ 2 ≠ 0 := by positivity
        have : (2 * θ + θ * θ * ‖w‖ ^ 2) * ‖w‖ ^ 2 = μ / γ * ‖w‖ ^ 2 := by
          have : (2 * θ + θ * θ * ‖w‖ ^ 2) * ‖w‖ ^ 2 = (θ * ‖w‖ ^ 2) * (2 + θ * ‖w‖ ^ 2) := by ring
          rw [this, hθ]
          nlinarith [hρ2]
        exact mul_right_cancel₀ hn0 this
      simp only [smul_apply, add_apply, one_apply_eq_self, N, bracket, rankOne_apply, hκ, hws, smul_add, smul_smul]
      have h2 : γ * (μ / γ * (a / 2)) = 1 := by
        rw [hμ]; field_simp
      rw [mul_assoc, h2, one_smul, hw]
      abel
  exact hy.symm

end VSQhelpA3

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem solution (y s : H) (hy : y ≠ 0) (hs : s ≠ 0) :
    List.TFAE
      [∃ B : H →L[ℝ] H, IsSelfAdjoint B ∧ IsPositiveStrict B ∧ y = B s,
       ∃ C : H ≃L[ℝ] H, y = adjoint (C : H →L[ℝ] H) (C s),
       0 < ⟪y, s⟫_ℝ] := by
  tfae_have 1 → 3 := by
    rintro ⟨B, -, hB, rfl⟩
    exact hB s hs
  tfae_have 2 → 1 := by
    rintro ⟨C, hC⟩
    refine ⟨adjoint (C : H →L[ℝ] H) ∘L (C : H →L[ℝ] H), ?_, ?_, ?_⟩
    · rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
      intro x z
      show ⟪adjoint (C : H →L[ℝ] H) ((C : H →L[ℝ] H) x), z⟫_ℝ =
        ⟪x, adjoint (C : H →L[ℝ] H) ((C : H →L[ℝ] H) z)⟫_ℝ
      rw [adjoint_inner_left, adjoint_inner_right]
    · intro u hu
      simp only [coe_comp', Function.comp_apply, adjoint_inner_left, real_inner_self_eq_norm_sq]
      have : (C : H →L[ℝ] H) u ≠ 0 := by
        intro h0
        exact hu (C.injective (by simpa using h0))
      positivity
    · simpa using hC
  tfae_have 3 → 2 := fun h => VSQhelpA3.exists_C y s hs h
  tfae_finish
