-- Prove2me | solution 1 for WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/85db3f80-2cd0-5f31-92ac-11c738e7fb50

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open WeierstrassCurve

namespace K2L1

variable {F : Type*} [Field F]

theorem mem_stabilizer_iff_of_isShortNF (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E : WeierstrassCurve F) [E.IsShortNF] (ha₄ : E.a₄ ≠ 0) (ha₆ : E.a₆ ≠ 0)
    (C : VariableChange F) :
    C ∈ MulAction.stabilizer (VariableChange F) E ↔
      C.r = 0 ∧ C.s = 0 ∧ C.t = 0 ∧ (C.u : F) ^ 2 = 1 := by
  rw [MulAction.mem_stabilizer_iff]
  have hu : ((C.u⁻¹ : Fˣ) : F) ≠ 0 := (C.u⁻¹).ne_zero
  have hE₁ : E.a₁ = 0 := E.a₁_of_isShortNF
  have hE₂ : E.a₂ = 0 := E.a₂_of_isShortNF
  have hE₃ : E.a₃ = 0 := E.a₃_of_isShortNF
  constructor
  · intro h
    have h₁ : (C • E).a₁ = E.a₁ := by rw [h]
    have h₂ : (C • E).a₂ = E.a₂ := by rw [h]
    have h₃ : (C • E).a₃ = E.a₃ := by rw [h]
    have h₄ : (C • E).a₄ = E.a₄ := by rw [h]
    have h₆ : (C • E).a₆ = E.a₆ := by rw [h]
    rw [variableChange_a₁, hE₁, zero_add] at h₁

    have hs : C.s = 0 := by
      have : ((C.u⁻¹ : Fˣ) : F) * (2 * C.s) = 0 := h₁
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hu
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h h2
        · exact h

    have hr : C.r = 0 := by
      rw [variableChange_a₂, hE₂, hE₁, hs] at h₂
      have : ((C.u⁻¹ : Fˣ) : F) ^ 2 * (3 * C.r) = 0 := by
        rw [← h₂]; ring
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) hu
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h h3
        · exact h

    have ht : C.t = 0 := by
      rw [variableChange_a₃, hE₃, hE₁, hr] at h₃
      have : ((C.u⁻¹ : Fˣ) : F) ^ 3 * (2 * C.t) = 0 := by
        rw [← h₃]; ring
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h) hu
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h h2
        · exact h

    have h4 : ((C.u⁻¹ : Fˣ) : F) ^ 4 = 1 := by
      rw [variableChange_a₄, hE₁, hE₂, hE₃, hr, hs, ht] at h₄
      have : ((C.u⁻¹ : Fˣ) : F) ^ 4 * E.a₄ = 1 * E.a₄ := by linear_combination h₄
      exact mul_right_cancel₀ ha₄ this
    have h6 : ((C.u⁻¹ : Fˣ) : F) ^ 6 = 1 := by
      rw [variableChange_a₆, hE₁, hE₂, hE₃, hr, ht] at h₆
      have : ((C.u⁻¹ : Fˣ) : F) ^ 6 * E.a₆ = 1 * E.a₆ := by linear_combination h₆
      exact mul_right_cancel₀ ha₆ this
    have hinv2 : ((C.u⁻¹ : Fˣ) : F) ^ 2 = 1 := by
      have h8 : ((C.u⁻¹ : Fˣ) : F) ^ 8 = 1 := by
        calc ((C.u⁻¹ : Fˣ) : F) ^ 8 = (((C.u⁻¹ : Fˣ) : F) ^ 4) ^ 2 := by ring
          _ = 1 := by rw [h4, one_pow]
      have : ((C.u⁻¹ : Fˣ) : F) ^ 8 = ((C.u⁻¹ : Fˣ) : F) ^ 6 * ((C.u⁻¹ : Fˣ) : F) ^ 2 := by ring
      rw [this, h6, one_mul] at h8
      exact h8
    have hu2 : (C.u : F) ^ 2 = 1 := by
      have hmul : (C.u : F) * ((C.u⁻¹ : Fˣ) : F) = 1 := by
        rw [Units.val_inv_eq_inv_val, mul_inv_cancel₀ C.u.ne_zero]
      calc (C.u : F) ^ 2 = (C.u : F) ^ 2 * (((C.u⁻¹ : Fˣ) : F) ^ 2) := by rw [hinv2, mul_one]
        _ = ((C.u : F) * ((C.u⁻¹ : Fˣ) : F)) ^ 2 := by ring
        _ = 1 := by rw [hmul, one_pow]
    exact ⟨hr, hs, ht, hu2⟩
  · rintro ⟨hr, hs, ht, hu2⟩
    have hinv2 : ((C.u⁻¹ : Fˣ) : F) ^ 2 = 1 := by
      rw [Units.val_inv_eq_inv_val, inv_pow, hu2, inv_one]
    have hinv4 : ((C.u⁻¹ : Fˣ) : F) ^ 4 = 1 := by
      calc ((C.u⁻¹ : Fˣ) : F) ^ 4 = (((C.u⁻¹ : Fˣ) : F) ^ 2) ^ 2 := by ring
        _ = 1 := by rw [hinv2, one_pow]
    have hinv6 : ((C.u⁻¹ : Fˣ) : F) ^ 6 = 1 := by
      calc ((C.u⁻¹ : Fˣ) : F) ^ 6 = (((C.u⁻¹ : Fˣ) : F) ^ 2) ^ 3 := by ring
        _ = 1 := by rw [hinv2, one_pow]
    ext
    · rw [variableChange_a₁, hE₁, hs]; ring
    · rw [variableChange_a₂, hE₁, hE₂, hr, hs]; ring
    · rw [variableChange_a₃, hE₁, hE₃, hr, ht]; ring
    · rw [variableChange_a₄, hE₁, hE₂, hE₃, hr, hs, ht]
      linear_combination E.a₄ * hinv4
    · rw [variableChange_a₆, hE₁, hE₂, hE₃, hr, ht]
      linear_combination E.a₆ * hinv6

def stabilizerEquivSqEqOne (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E : WeierstrassCurve F) [E.IsShortNF] (ha₄ : E.a₄ ≠ 0) (ha₆ : E.a₆ ≠ 0) :
    MulAction.stabilizer (VariableChange F) E ≃ {u : Fˣ // (u : F) ^ 2 = 1} where
  toFun C := ⟨C.1.u, ((mem_stabilizer_iff_of_isShortNF h2 h3 E ha₄ ha₆ C.1).mp C.2).2.2.2⟩
  invFun u := ⟨⟨u.1, 0, 0, 0⟩,
    (mem_stabilizer_iff_of_isShortNF h2 h3 E ha₄ ha₆ _).mpr ⟨rfl, rfl, rfl, u.2⟩⟩
  left_inv C := by
    obtain ⟨hr, hs, ht, -⟩ := (mem_stabilizer_iff_of_isShortNF h2 h3 E ha₄ ha₆ C.1).mp C.2
    apply Subtype.ext
    ext
    · rfl
    · exact hr.symm
    · exact hs.symm
    · exact ht.symm
  right_inv u := rfl

theorem natCard_sqEqOne (h2 : (2 : F) ≠ 0) : Nat.card {u : Fˣ // (u : F) ^ 2 = 1} = 2 := by
  classical
  have hne : (1 : Fˣ) ≠ -1 := by
    intro h
    have h' : ((1 : Fˣ) : F) = ((-1 : Fˣ) : F) := congrArg Units.val h
    rw [Units.val_one, Units.val_neg, Units.val_one] at h'
    apply h2
    linear_combination h'
  let e : {u : Fˣ // (u : F) ^ 2 = 1} ≃ Bool :=
    { toFun := fun u => decide (u.1 = 1)
      invFun := fun b => if b then ⟨1, by simp⟩ else ⟨-1, by simp⟩
      left_inv := by
        rintro ⟨u, hu⟩
        have hu' : (u : F) = 1 ∨ (u : F) = -1 := by
          rw [← mul_self_eq_one_iff, ← sq]; exact hu
        rcases hu' with h | h
        · have : u = 1 := Units.ext (by simpa using h)
          subst this; simp
        · have : u = -1 := Units.ext (by simpa using h)
          subst this
          simp [hne.symm]
      right_inv := by
        intro b
        cases b
        · simp [hne.symm]
        · simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_bool]

end K2L1

open K2L1 in
theorem solution
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E : WeierstrassCurve F) [E.IsElliptic] (hj0 : E.j ≠ 0) (hj1728 : E.j ≠ 1728) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) = 2 := by
  letI : Invertible (2 : F) := invertibleOfNonzero h2
  letI : Invertible (3 : F) := invertibleOfNonzero h3

  have hj : (E.toShortNF • E).j = E.j := variableChange_j E E.toShortNF

  have hΔ : (E.toShortNF • E).Δ ≠ 0 := by
    rw [← WeierstrassCurve.coe_Δ']; exact (E.toShortNF • E).Δ'.ne_zero
  have hden : 4 * (E.toShortNF • E).a₄ ^ 3 + 27 * (E.toShortNF • E).a₆ ^ 2 ≠ 0 := by
    intro h0
    apply hΔ
    rw [(E.toShortNF • E).Δ_of_isShortNF, h0, mul_zero]
  have ha₄ : (E.toShortNF • E).a₄ ≠ 0 := by
    intro h0
    apply hj0
    rw [← hj, (E.toShortNF • E).j_of_isShortNF, h0]
    simp
  have ha₆ : (E.toShortNF • E).a₆ ≠ 0 := by
    intro h0
    apply hj1728
    rw [← hj, (E.toShortNF • E).j_of_isShortNF, h0]
    have h4 : (4 : F) * (E.toShortNF • E).a₄ ^ 3 ≠ 0 := by
      rw [h0] at hden; simpa using hden
    rw [show (4 : F) * (E.toShortNF • E).a₄ ^ 3 + 27 * (0 : F) ^ 2
        = 4 * (E.toShortNF • E).a₄ ^ 3 by ring, div_eq_iff h4]
    ring

  have e1 : MulAction.stabilizer (VariableChange F) E
      ≃* MulAction.stabilizer (VariableChange F) (E.toShortNF • E) :=
    MulAction.stabilizerEquivStabilizer (g := E.toShortNF) rfl
  rw [Nat.card_congr e1.toEquiv,
    Nat.card_congr (stabilizerEquivSqEqOne h2 h3 (E.toShortNF • E) ha₄ ha₆), natCard_sqEqOne h2]

end

end S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728
end P2MW
export P2MW.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728 (solution)
