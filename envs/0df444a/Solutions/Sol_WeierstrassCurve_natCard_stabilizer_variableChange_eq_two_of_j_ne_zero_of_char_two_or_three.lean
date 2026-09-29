-- Prove2me | solution 1 for WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/0f9474e1-ea8e-5c31-bf43-5b75524b42a8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three

namespace AutCardCharTwoThree

open WeierstrassCurve

variable {F : Type*} [Field F]

def ofUnit (u : Fˣ) : VariableChange F := ⟨u, 0, 0, 0⟩

@[scoped simp] lemma ofUnit_u (u : Fˣ) : (ofUnit u).u = u := rfl
@[scoped simp] lemma ofUnit_r (u : Fˣ) : (ofUnit u).r = 0 := rfl
@[scoped simp] lemma ofUnit_s (u : Fˣ) : (ofUnit u).s = 0 := rfl
@[scoped simp] lemma ofUnit_t (u : Fˣ) : (ofUnit u).t = 0 := rfl

lemma ofUnit_one : (ofUnit 1 : VariableChange F) = 1 := by
  rw [VariableChange.one_def]; rfl

lemma mem_stab_iff (C : VariableChange F) (W : WeierstrassCurve F) :
    C ∈ MulAction.stabilizer (VariableChange F) W ↔ C • W = W :=
  MulAction.mem_stabilizer_iff

lemma natCard_stabilizer_eq_two (W : WeierstrassCurve F) (σ : VariableChange F)
    (hσ : σ • W = W) (hσ1 : σ ≠ 1)
    (hall : ∀ C : VariableChange F, C • W = W → C = 1 ∨ C = σ) :
    Nat.card (MulAction.stabilizer (VariableChange F) W) = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, (mem_stab_iff _ _).mpr (one_smul _ _)⟩, ⟨σ, (mem_stab_iff _ _).mpr hσ⟩,
    fun h => hσ1 (congrArg Subtype.val h).symm, ?_⟩
  ext ⟨C, hC⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases hall C ((mem_stab_iff _ _).mp hC) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

section Char3

variable [CharP F 3] {E : WeierstrassCurve F}

private lemma three_eq_zero : (3 : F) = 0 := by
  simpa using CharP.cast_eq_zero F 3

private lemma two_ne_zero' : (2 : F) ≠ 0 := by
  intro h
  have h1 : (1 : F) = 0 := by linear_combination three_eq_zero (F := F) - h
  exact one_ne_zero h1

lemma c3_of_smul_eq [E.IsCharThreeJNeZeroNF] (ha₂ : E.a₂ ≠ 0) {C : VariableChange F}
    (hC : C • E = E) : C.r = 0 ∧ C.s = 0 ∧ C.t = 0 ∧ ((C.u : F) = 1 ∨ (C.u : F) = -1) := by
  have hv : ((C.u⁻¹ : Fˣ) : F) ≠ 0 := (C.u⁻¹).ne_zero
  have h1 : (C • E).a₁ = E.a₁ := by rw [hC]
  have h2 : (C • E).a₂ = E.a₂ := by rw [hC]
  have h3 : (C • E).a₃ = E.a₃ := by rw [hC]
  have h4 : (C • E).a₄ = E.a₄ := by rw [hC]
  rw [variableChange_a₁, a₁_of_isCharThreeJNeZeroNF] at h1
  rw [variableChange_a₂, a₁_of_isCharThreeJNeZeroNF] at h2
  rw [variableChange_a₃, a₃_of_isCharThreeJNeZeroNF, a₁_of_isCharThreeJNeZeroNF] at h3
  rw [variableChange_a₄, a₄_of_isCharThreeJNeZeroNF, a₃_of_isCharThreeJNeZeroNF,
    a₁_of_isCharThreeJNeZeroNF] at h4
  have hs : C.s = 0 := by
    have h := (mul_eq_zero.mp h1).resolve_left hv
    rcases mul_eq_zero.mp (by linear_combination h : (2 : F) * C.s = 0) with h' | h'
    · exact absurd h' two_ne_zero'
    · exact h'
  have ht : C.t = 0 := by
    have h := (mul_eq_zero.mp h3).resolve_left (pow_ne_zero 3 hv)
    rcases mul_eq_zero.mp (by linear_combination h : (2 : F) * C.t = 0) with h' | h'
    · exact absurd h' two_ne_zero'
    · exact h'
  have hr : C.r = 0 := by
    have h := (mul_eq_zero.mp h4).resolve_left (pow_ne_zero 4 hv)
    rw [hs, ht] at h
    have h' : (2 * E.a₂) * C.r = 0 := by
      linear_combination h - C.r ^ 2 * three_eq_zero (F := F)
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' (mul_ne_zero two_ne_zero' ha₂)
    · exact h''
  have hu : ((C.u⁻¹ : Fˣ) : F) ^ 2 = 1 := by
    rw [hs, hr] at h2
    have h' : (((C.u⁻¹ : Fˣ) : F) ^ 2 - 1) * E.a₂ = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h' with h'' | h''
    · linear_combination h''
    · exact absurd h'' ha₂
  have hu' : (C.u : F) ^ 2 = 1 := by
    have := congrArg (fun z : F => z * (C.u : F) ^ 2) hu
    simp only [one_mul] at this
    rw [← this, ← mul_pow, Units.inv_mul, one_pow]
  exact ⟨hr, hs, ht, sq_eq_one_iff.mp hu'⟩

omit [CharP F 3] in

lemma c3_ofUnit_smul [E.IsCharThreeJNeZeroNF] (u : Fˣ) (hu : (u : F) = 1 ∨ (u : F) = -1) :
    ofUnit u • E = E := by
  have hv2 : ((u⁻¹ : Fˣ) : F) ^ 2 = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow]
    rcases hu with h | h <;> rw [h] <;> norm_num
  have hv6 : ((u⁻¹ : Fˣ) : F) ^ 6 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, hv2, one_pow]
  ext
  · simp only [variableChange_a₁, ofUnit_u, ofUnit_s, a₁_of_isCharThreeJNeZeroNF]
    ring
  · simp only [variableChange_a₂, ofUnit_u, ofUnit_r, ofUnit_s, a₁_of_isCharThreeJNeZeroNF]
    linear_combination E.a₂ * hv2
  · simp only [variableChange_a₃, ofUnit_u, ofUnit_r, ofUnit_t, a₃_of_isCharThreeJNeZeroNF,
      a₁_of_isCharThreeJNeZeroNF]
    ring
  · simp only [variableChange_a₄, ofUnit_u, ofUnit_r, ofUnit_s, ofUnit_t,
      a₄_of_isCharThreeJNeZeroNF, a₃_of_isCharThreeJNeZeroNF, a₁_of_isCharThreeJNeZeroNF]
    ring
  · simp only [variableChange_a₆, ofUnit_u, ofUnit_r, ofUnit_t,
      a₄_of_isCharThreeJNeZeroNF, a₃_of_isCharThreeJNeZeroNF, a₁_of_isCharThreeJNeZeroNF]
    linear_combination E.a₆ * hv6

theorem c3_jne_card [E.IsCharThreeJNeZeroNF] [E.IsElliptic] :
    Nat.card (MulAction.stabilizer (VariableChange F) E) = 2 := by
  have ha₂ : E.a₂ ≠ 0 := by
    intro h
    have hΔ := E.isUnit_Δ.ne_zero
    rw [Δ_of_isCharThreeJNeZeroNF_of_char_three, h] at hΔ
    simp at hΔ
  refine natCard_stabilizer_eq_two E (ofUnit (-1)) (c3_ofUnit_smul (-1) (Or.inr (by simp)))
    ?_ ?_
  · intro h
    have h' : ((ofUnit (-1) : VariableChange F)).u = (1 : VariableChange F).u := by rw [h]
    simp only [ofUnit_u, VariableChange.one_def] at h'
    have h'' : ((-1 : Fˣ) : F) = ((1 : Fˣ) : F) := by rw [h']
    simp only [Units.val_neg, Units.val_one] at h''
    exact two_ne_zero' (F := F) (by linear_combination -h'')
  · intro C hC
    obtain ⟨hr, hs, ht, hu | hu⟩ := c3_of_smul_eq ha₂ hC
    · left
      rw [VariableChange.one_def]
      ext <;> simp [hr, hs, ht, hu]
    · right
      ext <;> simp [hr, hs, ht, hu, ofUnit]

theorem card_stabilizer_char_three (W : WeierstrassCurve F) [W.IsElliptic] (hj : W.j ≠ 0) :
    Nat.card (MulAction.stabilizer (VariableChange F) W) = 2 := by
  obtain ⟨C, hC⟩ := W.exists_variableChange_isCharThreeNF
  rw [Nat.card_congr (MulAction.stabilizerEquivStabilizer (rfl : C • W = C • W)).toEquiv]
  cases hC with
  | of_j_ne_zero => exact c3_jne_card
  | of_j_eq_zero =>
    exact absurd ((variableChange_j W C).symm.trans (j_of_isShortNF_of_char_three (C • W))) hj

end Char3

section Char2

variable [CharP F 2] {E : WeierstrassCurve F}

private lemma two_eq_zero : (2 : F) = 0 := by
  simpa using CharP.cast_eq_zero F 2

def sigma : VariableChange F := ⟨1, 0, 1, 0⟩

omit [CharP F 2] in
@[scoped simp] lemma sigma_u : (sigma : VariableChange F).u = 1 := rfl
omit [CharP F 2] in
@[scoped simp] lemma sigma_r : (sigma : VariableChange F).r = 0 := rfl
omit [CharP F 2] in
@[scoped simp] lemma sigma_s : (sigma : VariableChange F).s = 1 := rfl
omit [CharP F 2] in
@[scoped simp] lemma sigma_t : (sigma : VariableChange F).t = 0 := rfl

lemma c2_of_smul_eq [E.IsCharTwoJNeZeroNF] {C : VariableChange F} (hC : C • E = E) :
    C.u = 1 ∧ C.r = 0 ∧ C.t = 0 ∧ (C.s = 0 ∨ C.s = 1) := by
  have h1 : (C • E).a₁ = E.a₁ := by rw [hC]
  have h2 : (C • E).a₂ = E.a₂ := by rw [hC]
  have h3 : (C • E).a₃ = E.a₃ := by rw [hC]
  have h4 : (C • E).a₄ = E.a₄ := by rw [hC]
  rw [variableChange_a₁, a₁_of_isCharTwoJNeZeroNF] at h1
  rw [variableChange_a₂, a₁_of_isCharTwoJNeZeroNF] at h2
  rw [variableChange_a₃, a₃_of_isCharTwoJNeZeroNF, a₁_of_isCharTwoJNeZeroNF] at h3
  rw [variableChange_a₄, a₄_of_isCharTwoJNeZeroNF, a₃_of_isCharTwoJNeZeroNF,
    a₁_of_isCharTwoJNeZeroNF] at h4
  have hv : ((C.u⁻¹ : Fˣ) : F) = 1 := by
    linear_combination h1 - ((C.u⁻¹ : Fˣ) : F) * C.s * two_eq_zero (F := F)
  have hu : C.u = 1 := by
    have : C.u⁻¹ = 1 := Units.ext (by simpa using hv)
    simpa using this
  rw [hv] at h2 h3 h4
  have hr : C.r = 0 := by
    linear_combination h3 - C.t * two_eq_zero (F := F)
  have ht : C.t = 0 := by
    rw [hr] at h4
    linear_combination -h4 - C.s * C.t * two_eq_zero (F := F)
  have hs : C.s * (C.s - 1) = 0 := by
    rw [hr] at h2
    linear_combination -h2 - C.s * two_eq_zero (F := F)
  refine ⟨hu, hr, ht, ?_⟩
  rcases mul_eq_zero.mp hs with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination h)

lemma c2_smul_of [E.IsCharTwoJNeZeroNF] (C : VariableChange F) (hu : C.u = 1) (hr : C.r = 0)
    (ht : C.t = 0) (hs : C.s = 0 ∨ C.s = 1) : C • E = E := by
  have hs' : C.s ^ 2 = C.s := by
    rcases hs with h | h <;> rw [h] <;> norm_num
  ext
  · simp only [variableChange_a₁, a₁_of_isCharTwoJNeZeroNF, hu, inv_one, Units.val_one, one_mul]
    linear_combination C.s * two_eq_zero (F := F)
  · simp only [variableChange_a₂, a₁_of_isCharTwoJNeZeroNF, hu, hr, inv_one, Units.val_one,
      one_pow, one_mul]
    linear_combination -hs' - C.s * two_eq_zero (F := F)
  · simp [variableChange_a₃, hu, hr, ht]
  · simp [variableChange_a₄, hu, hr, ht]
  · simp [variableChange_a₆, hu, hr, ht]

theorem c2_jne_card [E.IsCharTwoJNeZeroNF] :
    Nat.card (MulAction.stabilizer (VariableChange F) E) = 2 := by
  refine natCard_stabilizer_eq_two E sigma (c2_smul_of sigma rfl rfl rfl (Or.inr rfl)) ?_ ?_
  · intro h
    have h' : (sigma : VariableChange F).s = (1 : VariableChange F).s := by rw [h]
    simp only [sigma_s, VariableChange.one_def] at h'
    exact one_ne_zero h'
  · intro C hC
    obtain ⟨hu, hr, ht, hs | hs⟩ := c2_of_smul_eq hC
    · left
      rw [VariableChange.one_def]
      ext <;> simp [hr, hs, ht, hu]
    · right
      ext <;> simp [hr, hs, ht, hu, sigma]

theorem card_stabilizer_char_two (W : WeierstrassCurve F) [W.IsElliptic] (hj : W.j ≠ 0) :
    Nat.card (MulAction.stabilizer (VariableChange F) W) = 2 := by
  obtain ⟨C, hC⟩ := W.exists_variableChange_isCharTwoNF
  rw [Nat.card_congr (MulAction.stabilizerEquivStabilizer (rfl : C • W = C • W)).toEquiv]
  cases hC with
  | of_j_ne_zero => exact c2_jne_card
  | of_j_eq_zero =>
    exact absurd ((variableChange_j W C).symm.trans
      (j_of_isCharTwoJEqZeroNF_of_char_two (C • W))) hj

end Char2

theorem card_stabilizer_of_char_two_or_three (hF : ringChar F = 2 ∨ ringChar F = 3)
    (W : WeierstrassCurve F) [W.IsElliptic] (hj : W.j ≠ 0) :
    Nat.card (MulAction.stabilizer (VariableChange F) W) = 2 := by
  rcases hF with h | h
  · haveI : CharP F 2 := ringChar.of_eq h
    exact card_stabilizer_char_two W hj
  · haveI : CharP F 3 := ringChar.of_eq h
    exact card_stabilizer_char_three W hj

end AutCardCharTwoThree
p2m_reactivate "P2MW.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three.AutCardCharTwoThree"

open AutCardCharTwoThree in
theorem solution
    {F : Type*} [Field F] (hF : ringChar F = 2 ∨ ringChar F = 3)
    (E : WeierstrassCurve F) [E.IsElliptic] (hj0 : E.j ≠ 0) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) = 2 :=
  card_stabilizer_of_char_two_or_three hF E hj0

end S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three
end P2MW
export P2MW.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three (solution)
